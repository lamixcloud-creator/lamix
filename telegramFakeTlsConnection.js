'use strict';

const crypto = require('crypto');

// GramJS has a few circular CommonJS imports between connection internals.
// Loading the public entry first keeps those classes initialized.
require('telegram');

const { ObfuscatedConnection, PacketCodec } = require('telegram/network/connection/Connection');
const { TCPMTProxy } = require('telegram/network/connection/TCPMTProxy');
const { CTR } = require('telegram/crypto/CTR');
const { sha256 } = require('telegram/Helpers');

const DEBUG_FAKE_TLS = process.env.YUCHAT_TELEGRAM_FAKE_TLS_DEBUG === '1';

function debugFakeTls(...args) {
  if (DEBUG_FAKE_TLS) {
    console.error('[telegram-fake-tls]', ...args);
  }
}

function randomBytes(size) {
  return crypto.randomBytes(Math.max(1, Math.trunc(Number(size || 0)) || 1));
}

function hmacSha256(key, data) {
  return crypto.createHmac('sha256', key).update(data).digest();
}

function uint16(value) {
  const buffer = Buffer.alloc(2);
  buffer.writeUInt16BE(Math.max(0, Math.min(0xffff, Number(value || 0) || 0)), 0);
  return buffer;
}

function unixTimeLeXoredWithDigest(digest) {
  const time = Buffer.alloc(4);
  time.writeUInt32LE(Math.floor(Date.now() / 1000), 0);
  return Buffer.from([
    time[0] ^ digest[28],
    time[1] ^ digest[29],
    time[2] ^ digest[30],
    time[3] ^ digest[31]
  ]);
}

function randomX25519LikePublicKey() {
  return randomBytes(32);
}

function parseFakeTlsSecret(secret = '') {
  const normalized = String(secret || '').replace(/\s+/g, '').toLowerCase();
  if (!/^[0-9a-f]+$/i.test(normalized) || !normalized.startsWith('ee') || normalized.length <= 34 || normalized.length % 2 !== 0) {
    throw new Error('Invalid Fake TLS MTProxy secret.');
  }
  const full = Buffer.from(normalized, 'hex');
  const secretKey = full.subarray(1, 17);
  const domain = full.subarray(17);
  if (secretKey.length !== 16 || !domain.length) {
    throw new Error('Invalid Fake TLS MTProxy secret.');
  }
  return {
    full,
    secretKey,
    domain
  };
}

class MTProxyFakeTlsClientCodec {
  constructor(secret) {
    const parsed = Buffer.isBuffer(secret)
      ? {
          full: secret,
          secretKey: secret.subarray(1, 17),
          domain: secret.subarray(17)
        }
      : parseFakeTlsSecret(secret);
    this.fullSecret = parsed.full;
    this.secretKey = parsed.secretKey;
    this.domain = parsed.domain;
    this.sessionId = Buffer.alloc(32);
    this.clientRandom = Buffer.alloc(32);
    this.clientKeyShare = Buffer.alloc(32);
  }

  buildClientHello(randomOverride = null) {
    const domain = this.domain;
    const domainLength = domain.length;
    const random = Buffer.isBuffer(randomOverride) ? randomOverride : Buffer.alloc(32);
    const keyShare = Buffer.isBuffer(this.clientKeyShare) && this.clientKeyShare.length === 32
      ? this.clientKeyShare
      : Buffer.alloc(32);
    const parts = [
      Buffer.from('1603010200010001fc0303', 'hex'),
      random,
      Buffer.from('20', 'hex'),
      this.sessionId,
      Buffer.from('0020fafa130113021303c02bc02fc02cc030cca9cca8c013c014009c009d002f00350100', 'hex'),
      uint16(403),
      Buffer.from('4a4a00000000', 'hex'),
      uint16(2 + 1 + 2 + domainLength),
      uint16(1 + 2 + domainLength),
      Buffer.from('00', 'hex'),
      uint16(domainLength),
      domain,
      Buffer.from(
        '00170000ff01000100000a000a0008baba001d00170018'
        + '000b00020100002300000010000e000c02683208687474702f312e31'
        + '000500050100000000000d0012001004030804040105030805050108060601'
        + '001200000033002b0029baba000100001d0020',
        'hex'
      ),
      keyShare,
      Buffer.from(
        '002d00020101002b000b0a9a9a0304030303020301'
        + '001b00030200021a1a0001000015',
        'hex'
      ),
      Buffer.alloc(2),
      Buffer.alloc(0)
    ];
    let packet = Buffer.concat(parts);
    const paddingLength = Math.max(0, 517 - packet.length);
    parts[parts.length - 2] = uint16(paddingLength);
    parts[parts.length - 1] = Buffer.alloc(paddingLength);
    packet = Buffer.concat(parts);
    return packet;
  }

  buildNewClientHelloPacket() {
    this.sessionId = randomBytes(32);
    this.clientKeyShare = randomX25519LikePublicKey();
    const zeroRandomPacket = this.buildClientHello(Buffer.alloc(32));
    const digest = hmacSha256(this.secretKey, zeroRandomPacket);
    this.clientRandom = Buffer.concat([
      digest.subarray(0, 28),
      unixTimeLeXoredWithDigest(digest)
    ]);
    return this.buildClientHello(this.clientRandom);
  }

  verifyServerHello(serverHello) {
    if (!Buffer.isBuffer(serverHello) || serverHello.length < 133) {
      return false;
    }
    if (serverHello[0] !== 0x16 || serverHello[127] !== 0x14 || serverHello[133] !== 0x17) {
      return false;
    }
    const serverRandomOffset = 11;
    const serverRandom = serverHello.subarray(serverRandomOffset, serverRandomOffset + 32);
    const sessionStart = serverRandomOffset + 32 + 1;
    if (!serverHello.subarray(sessionStart, sessionStart + 32).equals(this.sessionId)) {
      return false;
    }
    const serverHelloForDigest = Buffer.concat([
      serverHello.subarray(0, serverRandomOffset),
      Buffer.alloc(32),
      serverHello.subarray(serverRandomOffset + 32)
    ]);
    const expected = hmacSha256(this.secretKey, Buffer.concat([this.clientRandom, serverHelloForDigest]));
    return serverRandom.equals(expected);
  }
}

class FakeTlsSocketAdapter {
  constructor(upstream) {
    this.upstream = upstream;
    this.buffer = Buffer.alloc(0);
    this.firstPacket = false;
  }

  async readTlsRecord() {
    while (true) {
      const recordType = await this.upstream.readExactly(1);
      if (!recordType?.length) {
        return Buffer.alloc(0);
      }
      const version = await this.upstream.readExactly(2);
      if (!version.equals(Buffer.from('0303', 'hex'))) {
        throw new Error('Invalid Fake TLS record version.');
      }
      const dataLength = (await this.upstream.readExactly(2)).readUInt16BE(0);
      const data = await this.upstream.readExactly(dataLength);
      debugFakeTls('read tls record', recordType[0], dataLength, data.subarray(0, 16).toString('hex'));
      if (recordType[0] === 0x14) {
        continue;
      }
      if (recordType[0] !== 0x17) {
        throw new Error('Invalid Fake TLS record type.');
      }
      return data;
    }
  }

  async readExactly(size) {
    let remaining = Math.max(0, Math.trunc(Number(size || 0)) || 0);
    while (this.buffer.length < remaining) {
      const next = await this.readTlsRecord();
      if (!next.length) {
        return Buffer.alloc(0);
      }
      this.buffer = Buffer.concat([this.buffer, next]);
    }
    const output = this.buffer.subarray(0, remaining);
    this.buffer = this.buffer.subarray(remaining);
    return output;
  }

  async read(size) {
    return this.readExactly(size);
  }

  write(data) {
    const buffer = Buffer.from(data || Buffer.alloc(0));
    const maxChunkSize = 16384 + 24;
    if (!this.firstPacket) {
      this.firstPacket = true;
      this.upstream.write(Buffer.from('140303000101', 'hex'));
      debugFakeTls('write tls change-cipher');
    }
    for (let offset = 0; offset < buffer.length; offset += maxChunkSize) {
      const chunk = buffer.subarray(offset, Math.min(offset + maxChunkSize, buffer.length));
      debugFakeTls('write tls app', chunk.length, chunk.subarray(0, 16).toString('hex'));
      this.upstream.write(Buffer.concat([
        Buffer.from('170303', 'hex'),
        uint16(chunk.length),
        chunk
      ]));
    }
  }

  close() {
    return this.upstream.close();
  }

  toString() {
    return 'FakeTlsSocketAdapter';
  }
}

class RandomizedIntermediatePacketCodec extends PacketCodec {
  constructor(connection) {
    super(connection);
    this.obfuscateTag = RandomizedIntermediatePacketCodec.obfuscateTag;
  }

  encodePacket(data) {
    const payload = Buffer.from(data || Buffer.alloc(0));
    const paddingLength = crypto.randomInt(0, 4);
    const padding = paddingLength > 0 ? randomBytes(paddingLength) : Buffer.alloc(0);
    const packet = Buffer.concat([payload, padding]);
    const length = Buffer.alloc(4);
    length.writeInt32LE(packet.length, 0);
    debugFakeTls('encode randomized intermediate', packet.length, paddingLength, packet.subarray(0, 16).toString('hex'));
    return Buffer.concat([length, packet]);
  }

  async readPacket(reader) {
    const lengthBytes = await reader.read(4);
    if (!lengthBytes?.length || lengthBytes.length !== 4) {
      return Buffer.alloc(0);
    }
    const length = lengthBytes.readInt32LE(0);
    if (length < 0) {
      throw new Error('Invalid randomized intermediate packet length.');
    }
    const packetWithPadding = await reader.read(length);
    const paddingLength = packetWithPadding.length % 4;
    debugFakeTls('read randomized intermediate length', length, paddingLength);
    return paddingLength > 0
      ? packetWithPadding.subarray(0, packetWithPadding.length - paddingLength)
      : packetWithPadding;
  }
}

RandomizedIntermediatePacketCodec.obfuscateTag = Buffer.from('dddddddd', 'hex');

class ConnectionTCPMTProxyRandomizedIntermediate extends TCPMTProxy {
  constructor() {
    super(...arguments);
    this.PacketCodecClass = RandomizedIntermediatePacketCodec;
  }
}

async function readFakeTlsRecord(socket) {
  const header = await socket.readExactly(5);
  if (!header?.length) {
    return { type: 0, raw: Buffer.alloc(0), data: Buffer.alloc(0) };
  }
  if (header.length !== 5) {
    throw new Error('Invalid Fake TLS record header.');
  }
  const version = header.subarray(1, 3);
  if (![
    '0301',
    '0302',
    '0303',
    '0304'
  ].includes(version.toString('hex'))) {
    throw new Error('Invalid Fake TLS record version.');
  }
  const dataLength = header.readUInt16BE(3);
  const data = dataLength > 0 ? await socket.readExactly(dataLength) : Buffer.alloc(0);
  if (data.length !== dataLength) {
    throw new Error('Incomplete Fake TLS record.');
  }
  return {
    type: header[0],
    raw: Buffer.concat([header, data]),
    data
  };
}

async function readFakeTlsServerHello(socket) {
  const handshake = await readFakeTlsRecord(socket);
  if (handshake.type !== 0x16) {
    throw new Error('Unexpected Fake TLS handshake record.');
  }
  const changeCipher = await readFakeTlsRecord(socket);
  if (changeCipher.type !== 0x14) {
    throw new Error('Unexpected Fake TLS change cipher record.');
  }
  const application = await readFakeTlsRecord(socket);
  if (application.type !== 0x17) {
    throw new Error('Unexpected Fake TLS application record.');
  }
  return Buffer.concat([handshake.raw, changeCipher.raw, application.raw]);
}

class FakeTlsMTProxyIO {
  constructor(connection) {
    this.header = undefined;
    this.connection = connection.socket;
    this._packetClass = connection.PacketCodecClass;
    this._secret = connection._secret;
    this._dcId = connection._dcId;
  }

  async initHeader() {
    const secret = this._secret;
    if (!Buffer.isBuffer(secret) || secret.length !== 16) {
      throw new Error('MTProxy secret must be a hex-string representing 16 bytes');
    }

    const keywords = [
      Buffer.from('50567247', 'hex'),
      Buffer.from('474554', 'hex'),
      Buffer.from('504f5354', 'hex'),
      Buffer.from('eeeeeeee', 'hex')
    ];
    let random;
    while (true) {
      random = randomBytes(64);
      if (random[0] === 0xef || random.subarray(4, 8).equals(Buffer.alloc(4))) {
        continue;
      }
      if (!keywords.some((keyword) => keyword.equals(random.subarray(0, 4)))) {
        break;
      }
    }

    const randomReversed = Buffer.from(random.subarray(8, 56)).reverse();
    const encryptKey = await sha256(Buffer.concat([random.subarray(8, 40), secret]));
    const encryptIv = random.subarray(40, 56);
    const decryptKey = await sha256(Buffer.concat([randomReversed.subarray(0, 32), secret]));
    const decryptIv = randomReversed.subarray(32, 48);
    const encryptor = new CTR(encryptKey, encryptIv);
    const decryptor = new CTR(decryptKey, decryptIv);
    const dcIdBytes = Buffer.alloc(2);
    dcIdBytes.writeInt8(this._dcId, 0);

    random = Buffer.concat([
      random.subarray(0, 56),
      this._packetClass.obfuscateTag,
      dcIdBytes,
      random.subarray(62)
    ]);
    random = Buffer.concat([
      random.subarray(0, 56),
      Buffer.from(encryptor.encrypt(random).subarray(56, 64)),
      random.subarray(64)
    ]);
    this.header = random;
    this._encrypt = encryptor;
    this._decrypt = decryptor;
  }

  async read(size) {
    const data = await this.connection.readExactly(size);
    debugFakeTls('read obfuscated encrypted', data.length, data.subarray(0, 16).toString('hex'));
    return this._decrypt.encrypt(data);
  }

  write(data) {
    debugFakeTls('write obfuscated plain', data.length, Buffer.from(data || Buffer.alloc(0)).subarray(0, 16).toString('hex'));
    this.connection.write(this._encrypt.encrypt(data));
  }
}

class ConnectionTCPMTProxyFakeTLS extends ObfuscatedConnection {
  constructor({ ip, port, dcId, loggers, proxy, socket, testServers }) {
    if (!proxy?.ip || !proxy?.port || !proxy?.secret) {
      throw new Error('Fake TLS MTProxy connection requires proxy ip, port and secret.');
    }
    super({
      ip: proxy.ip,
      port: proxy.port,
      dcId,
      loggers,
      proxy: null,
      socket,
      testServers
    });
    const parsed = parseFakeTlsSecret(proxy.secret);
    this._fakeTlsSecret = parsed.full;
    this._secret = parsed.secretKey;
    this._proxy = proxy;
    this.ObfuscatedIO = FakeTlsMTProxyIO;
    this.PacketCodecClass = RandomizedIntermediatePacketCodec;
  }

  async _initConn() {
    const fakeTls = new MTProxyFakeTlsClientCodec(this._fakeTlsSecret);
    this.socket.write(fakeTls.buildNewClientHelloPacket());
    const serverHello = await readFakeTlsServerHello(this.socket);
    if (!fakeTls.verifyServerHello(serverHello)) {
      throw new Error('Fake TLS MTProxy handshake failed.');
    }
    this.socket = new FakeTlsSocketAdapter(this.socket);
    await super._initConn();
  }
}

module.exports = {
  ConnectionTCPMTProxyFakeTLS,
  ConnectionTCPMTProxyRandomizedIntermediate,
  MTProxyFakeTlsClientCodec
};
