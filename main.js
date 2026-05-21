const { app, BrowserWindow, ipcMain, Notification, shell, clipboard, session, desktopCapturer, dialog, systemPreferences, nativeImage, protocol, screen, globalShortcut } = require('electron');
const path = require('path');
const fs = require('fs');
const http = require('http');
const https = require('https');
const zlib = require('zlib');
const crypto = require('crypto');
const { spawn } = require('child_process');
const {
  normalizeStoredAuthStateSnapshot,
  hasStoredAuthState,
  buildStoredAuthStateSnapshot
} = require('./preload_architecture/authStateSnapshot');
const {
  normalizeAuthStateOrigin: normalizeAuthStateOriginPolicy,
  isTrustedAuthStateHostname: isTrustedAuthStateHostnamePolicy,
  getTrustedAuthStateOrigin: getTrustedAuthStateOriginPolicy
} = require('./preload_architecture/authStatePolicy');
const {
  normalizeShortcut: normalizeKeyboardShortcut = (shortcut = '') => String(shortcut || '').trim()
} = require('./preload_architecture/productivityLayer/keyboardShortcuts');
let bundledFfmpegPath = '';
try {
  bundledFfmpegPath = require('@ffmpeg-installer/ffmpeg')?.path || '';
} catch {
  bundledFfmpegPath = '';
}
let Store = null;
let systemNotificationPreferences = {
  yuchat: true,
  telegram: true
};

function installThirdPartyConsoleNoiseFilter() {
  if (!console || console.__yuThirdPartyNoiseFilterInstalled === true) return;
  const originalLog = typeof console.log === 'function' ? console.log.bind(console) : null;
  if (!originalLog) return;
  const ignoredMessages = new Set([
    'sender already has some hanging states. reconnecting'
  ]);
  console.log = (...args) => {
    if (
      args.length === 1
      && ignoredMessages.has(String(args[0] || '').trim())
    ) {
      return;
    }
    originalLog(...args);
  };
  Object.defineProperty(console, '__yuThirdPartyNoiseFilterInstalled', {
    value: true,
    enumerable: false,
    configurable: false
  });
}

installThirdPartyConsoleNoiseFilter();

function isPlainRecord(value = null) {
  return Boolean(value) && typeof value === 'object' && !Array.isArray(value);
}

function splitPath(pathKey = '') {
  return String(pathKey || '')
    .trim()
    .split('.')
    .map((part) => String(part || '').trim())
    .filter(Boolean);
}

function readNested(target = null, pathKey = '') {
  const parts = splitPath(pathKey);
  if (!parts.length) return target;
  let cursor = target;
  for (const part of parts) {
    if (!isPlainRecord(cursor)) return undefined;
    cursor = cursor[part];
  }
  return cursor;
}

function writeNested(target = null, pathKey = '', value = null) {
  const parts = splitPath(pathKey);
  if (!parts.length) return target;
  let cursor = target;
  for (let index = 0; index < parts.length - 1; index += 1) {
    const part = parts[index];
    if (!isPlainRecord(cursor[part])) {
      cursor[part] = {};
    }
    cursor = cursor[part];
  }
  cursor[parts[parts.length - 1]] = value;
  return target;
}

function deleteNested(target = null, pathKey = '') {
  const parts = splitPath(pathKey);
  if (!parts.length || !isPlainRecord(target)) return false;
  let cursor = target;
  for (let index = 0; index < parts.length - 1; index += 1) {
    const part = parts[index];
    if (!isPlainRecord(cursor[part])) return false;
    cursor = cursor[part];
  }
  const leaf = parts[parts.length - 1];
  if (!Object.prototype.hasOwnProperty.call(cursor, leaf)) return false;
  delete cursor[leaf];
  return true;
}

class FallbackJsonStore {
  constructor(options = {}) {
    const name = String(options?.name || 'store').trim() || 'store';
    const configuredCwd = String(options?.cwd || '').trim();
    const fallbackCwd = (() => {
      try {
        return app.getPath('userData');
      } catch {
        return process.cwd();
      }
    })();
    this.filePath = path.join(configuredCwd || fallbackCwd, `${name}.json`);
    this.data = {};
    this.load();
  }

  load() {
    try {
      const raw = fs.readFileSync(this.filePath, 'utf8');
      const parsed = JSON.parse(raw);
      this.data = isPlainRecord(parsed) ? parsed : {};
    } catch {
      this.data = {};
    }
  }

  save() {
    try {
      fs.mkdirSync(path.dirname(this.filePath), { recursive: true });
      fs.writeFileSync(this.filePath, JSON.stringify(this.data, null, 2), 'utf8');
      return true;
    } catch {
      return false;
    }
  }

  get(pathKey = '', defaultValue = undefined) {
    const value = readNested(this.data, pathKey);
    return typeof value === 'undefined' ? defaultValue : value;
  }

  set(pathKey = '', value = null) {
    writeNested(this.data, pathKey, value);
    this.save();
  }

  delete(pathKey = '') {
    if (deleteNested(this.data, pathKey)) {
      this.save();
    }
  }
}

try {
  Store = require('electron-store').default;
} catch {
  Store = FallbackJsonStore;
  console.warn('[YuChat] electron-store unavailable, using fallback JSON store');
}

try {
  app.commandLine.appendSwitch(
    'disable-features',
    'ThirdPartyStoragePartitioning,PartitionedCookies,ImprovedCookieControls,ThirdPartyCookiesPhaseout'
  );
} catch {
  // ignore Chromium flag setup issues
}

try {
  app.commandLine.appendSwitch('persist-session-cookies');
} catch {
  // ignore Chromium flag setup issues
}

let mainWindow;
let messengerWindowMode = 'normal';
let messengerWindowShortcut = 'cmd+shift+space';
let messengerWindowOpacity = 1;
let messengerWindowAnimationDurationMs = 320;
let mainWindowNormalBounds = null;
let mainWindowNormalIsMaximized = true;
let mainWindowBoundsCustomized = false;
let mainWindowReadyForBoundsTracking = false;
let messengerWindowExpandedBounds = null;
let registeredMessengerWindowShortcut = '';
let messengerWindowHideTimer = 0;
let messengerWindowAnimationDirection = '';
let messengerWindowIsHidden = false;
const activeNotifications = new Set();
const recentNotificationKeys = new Map();
const reminderNotificationTimers = new Map();
const knownChatTitles = new Map();
const knownChatAuthors = new Map();
const knownWorkspaceTitles = new Map();
const seenRealtimeMessageIds = new Set();
let activeConversationTitle = '';
let activeConversationChatId = '';
let activeWorkspaceId = '';
let currentUserName = '';
let currentUserMemberId = '';
let mainWindowShown = false;
let mainWindowAuthSurfaceVisible = false;
let mainWindowAuthSurfaceVisitedSso = false;
let mainWindowAuthTransitionActive = false;
let authTransitionSplashInFlight = null;
let mainWindowRevealFallbackTimer = 0;
let mainWindowRevealCloseTimer = 0;
let mainWindowPostRevealProbeTimer = 0;
let mainWindowRevealFallbackDeferrals = 0;
let startupSplashWindow = null;
let startupSplashReady = false;
let startupSplashClosing = false;
let trueconfAuthWindow = null;
let telegramWebWindow = null;
let telegramClient = null;
let telegramClientSignature = '';
let telegramPendingAuth = null;
let telegramPendingAuthPromise = null;
let telegramUpdateBridgeInstalledForClient = null;
const telegramOutgoingCallStateById = new Map();
let telegramWebDialogCache = [];
let telegramWebDialogCacheUpdatedAt = 0;
const telegramEntityCacheByKey = new Map();
const telegramMediaTokenToRecord = new Map();
const SMOKE_TEST_REQUESTED = process.argv.includes('--smoke-test');
const SHOULD_ENFORCE_SINGLE_INSTANCE = SMOKE_TEST_REQUESTED || app.isPackaged === true;
const YUCHAT_SESSION_PARTITION = 'persist:yuchat';
const YUCHAT_SESSION_COOKIE_STORE_KEY = 'sessionCookies';
const YUCHAT_STORAGE_NAME = 'YuchatCustom';
const CUSTOM_YUCHAT_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120 Safari/537.36';
const CORPORATE_PORTAL_ALLOWED_ORIGINS = new Set([
  'https://portal.rt.ru',
  'https://www.portal.rt.ru',
  'https://w3c.portal.rt.ru'
]);
const TRUECONF_ALLOWED_HOSTNAME_SUFFIX = '.trueconf.rt.ru';
const TRUECONF_PRIMARY_HOSTNAME = 'trueconf.rt.ru';
const TRUECONF_DEFAULT_TIMEOUT_MS = 15000;
const TRUECONF_MAX_LIST_PAGE_SIZE = 300;
const TRUECONF_CHAT_AUTH_STORE_KEY = 'trueconfChatIntegration';
const TRUECONF_CHAT_PREFIX = 'tc:';
const TRUECONF_CHAT_DEFAULT_PAGE_SIZE = 80;
const TRUECONF_CHAT_MAX_PAGE_SIZE = 200;
const TRUECONF_CHAT_WS_TIMEOUT_MS = 22000;
const TRUECONF_CHAT_BRIDGE_DISCOVERY_TIMEOUT_MS = 5500;
const TRUECONF_CHAT_BRIDGE_FALLBACK_PORTS = [4309];
const CORPORATE_PORTAL_FETCH_MAX_TEXT_LENGTH = 786432;
const YUCHAT_STORAGE_PROFILE_NAME = SMOKE_TEST_REQUESTED
  ? `${YUCHAT_STORAGE_NAME}-smoke`
  : YUCHAT_STORAGE_NAME;
const configuredYuchatSessions = new WeakSet();
const configuredOwaCaptureSessions = new WeakSet();
let yuchatSessionFlushTimer = 0;
let yuchatSessionFlushInFlight = null;
let yuchatSessionCookiesDirty = false;
let isQuittingAfterSessionFlush = false;
let appQuitFallbackTimer = 0;
const MAX_REMINDER_TIMER_DELAY_MS = 2_147_000_000;
const SESSION_FLUSH_ON_QUIT_TIMEOUT_MS = 2500;
const localAssetDataUrlCache = new Map();
const LOCAL_ASSET_PROTOCOL = 'yuchat-resource';
const attachmentPreviewTokenToRecord = new Map();
const attachmentPreviewCacheByKey = new Map();
const favoritesPlayableVideoPromiseByKey = new Map();
const telegramAvatarDataUrlCache = new Map();
const notificationIconCache = new Map();
const notificationIconPending = new Map();
const NOTIFICATION_ICON_CACHE_TTL_MS = 5 * 60 * 1000;
const latestMainFrameStatusByWebContentsId = new Map();
const DEFAULT_STARTUP_SPLASH_STATE = Object.freeze({
  percent: 6,
  phase: 'Запускаем YuChat',
  detail: 'Готовим защищённое рабочее пространство'
});
let startupSplashState = { ...DEFAULT_STARTUP_SPLASH_STATE };
const STARTUP_SPLASH_CLOSE_DELAY_MS = 220;
const MAIN_WINDOW_REVEAL_TIMEOUT_MS = 20000;
const MAIN_WINDOW_REVEAL_SETTLE_DELAY_MS = 320;
const STARTUP_PROGRESS_STALL_FALLBACK_MS = 22000;
const STARTUP_PROGRESS_STALL_RETRY_MS = 15000;
const STARTUP_PROGRESS_STALL_MAX_DEFERRALS = 4;
const STARTUP_GLOBAL_REVEAL_FALLBACK_MS = 90000;
const PRELOAD_HEARTBEAT_GRACE_WINDOW_MS = 120000;
let localAssetProtocolRegistered = false;
const owaWindowsByOrigin = new Map();
let owaRequestSequence = 0;
const OWA_AUTO_CONNECT_REVEAL_DELAY_MS = 5000;
const OWA_PROMPT_WINDOW_WIDTH = 560;
const OWA_PROMPT_WINDOW_HEIGHT = 420;
const owaPendingCertificatePromptByKey = new Map();
const owaPendingBasicAuthPromptByKey = new Map();

protocol.registerSchemesAsPrivileged([
  {
    scheme: LOCAL_ASSET_PROTOCOL,
    privileges: {
      standard: true,
      secure: true,
      supportFetchAPI: true,
      corsEnabled: true,
      stream: true
    }
  }
]);
const FULL_CUSTOM_PRELOAD_PATH = path.join(__dirname, 'preloadBootstrap.js');
const LOCAL_SHELL_ENTRY_PATH = path.join(__dirname, 'index.html');
const LOCAL_SHELL_PRELOAD_PATH = path.join(__dirname, 'preload.js');
const LEGACY_PRELOAD_PATH = path.join(__dirname, 'highlightPreload.js');
const STARTUP_SPLASH_ENTRY_PATH = path.join(__dirname, 'startupSplash.html');
const LOCAL_SHELL_REQUESTED = (
  process.argv.includes('--local-shell')
  || process.env.YUCHAT_LOCAL_SHELL === '1'
);
const LEGACY_PRELOAD_REQUESTED = (
  process.argv.includes('--legacy-preload')
  || process.env.YUCHAT_USE_LEGACY_PRELOAD === '1'
);
const LEGACY_PRELOAD_AVAILABLE = fs.existsSync(LEGACY_PRELOAD_PATH);
const USE_LEGACY_PRELOAD = LEGACY_PRELOAD_REQUESTED && LEGACY_PRELOAD_AVAILABLE;
const YUCHAT_PRELOAD_PATH = USE_LEGACY_PRELOAD
  ? LEGACY_PRELOAD_PATH
  : FULL_CUSTOM_PRELOAD_PATH;
const WINDOW_PRELOAD_PATH = LOCAL_SHELL_REQUESTED
  ? LOCAL_SHELL_PRELOAD_PATH
  : YUCHAT_PRELOAD_PATH;
const WINDOW_SANDBOX_ENABLED = LOCAL_SHELL_REQUESTED;
const WINDOW_STATE_FILE_NAME = 'window-state.json';
const WINDOW_MODE_NORMAL = 'normal';
const WINDOW_MODE_MESSENGER = 'messenger';
const DEFAULT_MESSENGER_SHORTCUT = 'cmd+shift+space';
const DEFAULT_MESSENGER_OPACITY = 1;
const MIN_MESSENGER_OPACITY = 0.4;
const MAX_MESSENGER_OPACITY = 1;
const DEFAULT_MESSENGER_ANIMATION_DURATION_MS = 320;
const MIN_MESSENGER_ANIMATION_DURATION_MS = 120;
const MAX_MESSENGER_ANIMATION_DURATION_MS = 1200;
const MESSENGER_WINDOW_ANIMATION_FRAME_MS = 1000 / 90;
const MAIN_WINDOW_MIN_WIDTH = 1180;
const MAIN_WINDOW_MIN_HEIGHT = 720;
const MESSENGER_WINDOW_MIN_WIDTH = 320;
const MESSENGER_WINDOW_COLLAPSED_HEIGHT = 1;
const MESSENGER_WINDOW_HEIGHT_RATIO = 0.56;
const MESSENGER_WINDOW_MIN_HEIGHT = 420;
const MESSENGER_WINDOW_HIDE_PEEK_PX = 0;
const AUTH_STATE_STORE_NAME = 'auth-state';
const VOSK_PYTHON_PACKAGE_SPEC = 'vosk==0.3.44';
const VOSK_PYTHON_PACKAGE_VERSION = '0.3.44';
const VOSK_CFFI_PACKAGE_VERSION = '1.17.1';
const VOSK_PYCPARSER_PACKAGE_VERSION = '2.22';
const VOSK_MODEL_NAME = 'vosk-model-small-ru-0.22';
const VOSK_MODEL_URL = 'https://alphacephei.com/vosk/models/vosk-model-small-ru-0.22.zip';
const VOSK_MODEL_FALLBACK_URLS = [
  'https://huggingface.co/rhasspy/vosk-models/resolve/main/ru/vosk-model-small-ru-0.22.zip',
  'https://github.com/kercre123/vosk-models/raw/main/vosk-model-small-ru-0.22.zip'
];
const VOSK_METADATA_FETCH_TIMEOUT_MS = 20000;
const VOSK_DOWNLOAD_CONNECT_TIMEOUT_MS = 30000;
const VOSK_DOWNLOAD_IDLE_TIMEOUT_MS = 45000;
const VOSK_HELPER_SOURCE_PATH = path.join(__dirname, 'scripts', 'vosk_dictation.py');
const VOSK_HELPER_FILE_NAME = 'vosk_dictation_runtime.py';
const TELEGRAM_WEB_URL = 'https://web.telegram.org/a/';
const TELEGRAM_WEB_HOSTNAME = 'web.telegram.org';
const TELEGRAM_WEB_PARTITION = 'persist:telegram-web';
const MAX_WEB_HOSTNAME = 'web.max.ru';
const MAX_WEB_PARTITION = 'persist:max-web';
const TELEGRAM_AUTH_STORE_KEY = 'telegramIntegration';
const TELEGRAM_DEFAULT_DIALOG_LIMIT = 80;
const TELEGRAM_WEB_A_API_ID = 2496;
const TELEGRAM_WEB_A_API_HASH = '8da85b0d5bfe62527e5b244c209159c3';
const TELEGRAM_WEB_A_DEVICE_MODEL = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/144.0.0.0 Safari/537.36';
const TELEGRAM_WEB_A_SYSTEM_VERSION = 'Windows';
const TELEGRAM_WEB_A_APP_VERSION = '5.0.0 A';
const TELEGRAM_DC_ADDRESS_BY_ID = {
  1: '149.154.175.53',
  2: '149.154.167.51',
  3: '149.154.175.100',
  4: '149.154.167.91',
  5: '91.108.56.130'
};
const TELEGRAM_CONNECT_TIMEOUT_MS = 22000;
const TELEGRAM_SEND_CODE_TIMEOUT_MS = 90000;
const TELEGRAM_SIGN_IN_TIMEOUT_MS = 35000;
const TELEGRAM_DIALOGS_TIMEOUT_MS = 45000;
const TELEGRAM_MESSAGES_TIMEOUT_MS = 45000;
const TELEGRAM_SEND_TIMEOUT_MS = 45000;
const TELEGRAM_MEDIA_DOWNLOAD_TIMEOUT_MS = 90000;
const TELEGRAM_AVATAR_DOWNLOAD_TIMEOUT_MS = 7000;
const TELEGRAM_DIALOG_AVATAR_LIMIT = 180;
const TELEGRAM_DIALOG_AVATAR_CONCURRENCY = 8;
const TELEGRAM_DIALOG_AVATAR_BUDGET_MS = 26000;
const TELEGRAM_PROFILE_TIMEOUT_MS = 9000;
const TELEGRAM_DIALOG_PINNED_AT = '1970-01-01T00:00:01.000Z';
const TELEGRAM_DIALOG_PREFIX = 'tg:';
const TELEGRAM_CALL_MIN_LAYER = 65;
const TELEGRAM_CALL_MAX_LAYER = 92;
const TELEGRAM_CALL_LIBRARY_VERSIONS = Object.freeze(['2.7.7', '2.4.4']);
// MTProto can request/confirm Telegram calls; audio still needs a tgcalls media engine.
const TELEGRAM_CALL_MEDIA_ENGINE_AVAILABLE = false;
const VOSK_STUB_REQUESTS_SOURCE = `class _Response:
    def __init__(self):
        self.status_code = 599

    def json(self):
        raise RuntimeError("requests недоступен в встроенном Vosk runtime")


def get(*args, **kwargs):
    raise RuntimeError("requests недоступен в встроенном Vosk runtime")


def post(*args, **kwargs):
    raise RuntimeError("requests недоступен в встроенном Vosk runtime")
`;
const VOSK_STUB_SRT_SOURCE = `class Subtitle:
    def __init__(self, index=0, content="", start=None, end=None):
        self.index = index
        self.content = content
        self.start = start
        self.end = end


def compose(entries):
    return "\\n".join(str(getattr(entry, "content", "")) for entry in (entries or []))
`;
const VOSK_STUB_TQDM_SOURCE = `class tqdm:
    def __init__(self, *args, **kwargs):
        self.total = kwargs.get("total")
        self.n = 0

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False

    def update(self, step=0):
        self.n += int(step or 0)
        return self.n

    def close(self):
        return None
`;
const TRUSTED_AUTH_STATE_HOSTNAMES = new Set([
  'yuchat.rt.ru',
  'sso.keyid.rt.ru'
]);
const AUTH_STATE_STORE_CWD = (() => {
  try {
    return path.join(app.getPath('appData'), YUCHAT_STORAGE_PROFILE_NAME);
  } catch {
    return '';
  }
})();
const ALLOWED_RENDERER_PERMISSION_NAMES = new Set([
  'clipboard-read',
  'clipboard-sanitized-write',
  'display-capture',
  'fullscreen',
  'media',
  'notifications',
  // YuChat renews auth through cross-site SSO flows between yuchat.rt.ru and sso.keyid.rt.ru.
  'storage-access',
  'top-level-storage-access'
]);
const AUTH_STATE_POLICY_OPTIONS = {
  trustedHostnames: TRUSTED_AUTH_STATE_HOSTNAMES
};
const normalizeAuthStateOrigin = (origin = '') => normalizeAuthStateOriginPolicy(origin);
const isTrustedAuthStateHostname = (hostname = '') => (
  isTrustedAuthStateHostnamePolicy(hostname, AUTH_STATE_POLICY_OPTIONS)
);
const getTrustedAuthStateOrigin = (event = null, payload = {}) => (
  getTrustedAuthStateOriginPolicy(event, payload, AUTH_STATE_POLICY_OPTIONS)
);
function getYuchatEntryOrigin() {
  try {
    return new URL(YUCHAT_ENTRY_URL).origin;
  } catch {
    return 'https://yuchat.rt.ru';
  }
}

function isTrustedInAppHostname(hostname = '') {
  const normalized = String(hostname || '').trim().toLowerCase();
  if (!normalized) return false;

  const entryHostname = (() => {
    try {
      return new URL(getYuchatEntryOrigin()).hostname.toLowerCase();
    } catch {
      return 'yuchat.rt.ru';
    }
  })();

  return (
    normalized === entryHostname
    || normalized.endsWith(`.${entryHostname}`)
    || isTrustedAuthStateHostname(normalized)
  );
}

function isTrustedInAppUrl(targetUrl = '') {
  try {
    const parsed = new URL(String(targetUrl || '').trim());
    return /^https?:$/.test(parsed.protocol) && isTrustedInAppHostname(parsed.hostname);
  } catch {
    return false;
  }
}

function getYuchatEntryHostname() {
  try {
    return new URL(getYuchatEntryOrigin()).hostname.toLowerCase();
  } catch {
    return 'yuchat.rt.ru';
  }
}

function getUrlHostname(targetUrl = '') {
  try {
    return new URL(String(targetUrl || '').trim()).hostname.toLowerCase();
  } catch {
    return '';
  }
}

function isYuchatAppUrl(targetUrl = '') {
  const hostname = getUrlHostname(targetUrl);
  if (!hostname) return false;
  const entryHostname = getYuchatEntryHostname();
  return hostname === entryHostname || hostname.endsWith(`.${entryHostname}`);
}

function isYuchatSsoUrl(targetUrl = '') {
  const hostname = getUrlHostname(targetUrl);
  return hostname === 'sso.keyid.rt.ru';
}

function isYuchatAuthCallbackUrl(targetUrl = '') {
  try {
    const parsed = new URL(String(targetUrl || '').trim());
    if (!isYuchatAppUrl(parsed.href)) return false;
    const pathname = String(parsed.pathname || '').toLowerCase();
    if (!pathname.startsWith('/auth/')) return false;
    const authPayload = `${parsed.search || ''}&${parsed.hash || ''}`.toLowerCase();
    return authPayload.includes('code=') && !authPayload.includes('error=');
  } catch {
    return false;
  }
}

function isLocalAssetUrl(targetUrl = '') {
  try {
    const parsed = new URL(String(targetUrl || '').trim());
    return parsed.protocol === `${LOCAL_ASSET_PROTOCOL}:`;
  } catch {
    return false;
  }
}

function isSafeAttachmentUrl(targetUrl = '') {
  return isSafeExternalUrl(targetUrl) || isLocalAssetUrl(targetUrl);
}

function isAllowedRendererPermission(permission = '', details = {}) {
  const normalizedPermission = String(permission || '').trim().toLowerCase();
  if (normalizedPermission === 'notifications') {
    return false;
  }
  if (!ALLOWED_RENDERER_PERMISSION_NAMES.has(normalizedPermission)) {
    return false;
  }

  const candidateUrls = [
    details?.requestingUrl,
    details?.embeddingOrigin,
    details?.securityOrigin,
    details?.requestingOrigin
  ];

  const trustedRequest = candidateUrls.some((candidate) => (
    typeof candidate === 'string'
      && candidate.trim()
      && isTrustedInAppUrl(candidate)
  ));
  if (!trustedRequest && normalizedPermission !== 'notifications') {
    return false;
  }

  return true;
}

let mainWindowStatePersistTimer = 0;
let currentViewCapturePromise = null;
let currentViewCaptureCache = {
  dataUrl: '',
  capturedAt: 0
};
const CAPTURE_CURRENT_VIEW_CACHE_TTL_MS = 180;
const authStateStore = new Store({
  name: AUTH_STATE_STORE_NAME,
  clearInvalidConfig: true,
  ...(AUTH_STATE_STORE_CWD ? { cwd: AUTH_STATE_STORE_CWD } : {})
});

function getDialogOwnerWindow() {
  return mainWindow && !mainWindow.isDestroyed() ? mainWindow : undefined;
}

function escapeHtml(value = '') {
  return String(value || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function cleanTelegramText(value = '', maxLength = 240) {
  const normalized = String(value ?? '')
    .replace(/\s+/gu, ' ')
    .trim();
  const limit = Math.max(1, Number(maxLength || 240) || 240);
  return normalized.length > limit ? normalized.slice(0, limit).trim() : normalized;
}

function cleanTelegramMultiline(value = '', maxLength = 6000) {
  const normalized = String(value ?? '')
    .split(/\r?\n+/u)
    .map((line) => String(line || '').replace(/[^\S\r\n]+/gu, ' ').trim())
    .filter(Boolean)
    .join('\n')
    .trim();
  const limit = Math.max(1, Number(maxLength || 6000) || 6000);
  return normalized.length > limit ? normalized.slice(0, limit).trim() : normalized;
}

function getTelegramBundledApiCredentials() {
  const envApiId = Math.trunc(Number(process.env.YUCHAT_TELEGRAM_API_ID || 0) || 0);
  const envApiHash = cleanTelegramText(process.env.YUCHAT_TELEGRAM_API_HASH || '', 128);
  return {
    apiId: envApiId > 0 ? envApiId : TELEGRAM_WEB_A_API_ID,
    apiHash: envApiHash || TELEGRAM_WEB_A_API_HASH,
    source: envApiId > 0 && envApiHash ? 'env' : 'web_a'
  };
}

function normalizeTelegramApiSettings(source = null) {
  const input = isPlainRecord(source) ? source : {};
  const credentials = getTelegramBundledApiCredentials();
  const phoneNumber = cleanTelegramText(input.phoneNumber || input.phone || '', 64);
  const proxyUrl = cleanTelegramText(input.proxyUrl || input.proxy || input.mtproxyUrl || '', 1200);
  return {
    enabled: input.enabled === true,
    apiId: credentials.apiId,
    apiHash: credentials.apiHash,
    apiSource: credentials.source,
    phoneNumber,
    proxyUrl
  };
}

function getTelegramProxySecretMode(secret = '') {
  const normalized = cleanTelegramText(secret || '', 512).replace(/\s+/gu, '').toLowerCase();
  if (normalized.startsWith('ee')) return 'fake_tls';
  if (normalized.startsWith('dd')) return 'random_padding';
  return 'classic';
}

function decodeTelegramFakeTlsDomain(secret = '') {
  const normalized = cleanTelegramText(secret || '', 512).replace(/\s+/gu, '').toLowerCase();
  if (!normalized.startsWith('ee') || normalized.length <= 34 || normalized.length % 2 !== 0) {
    return '';
  }
  try {
    const domain = Buffer.from(normalized.slice(34), 'hex').toString('utf8');
    return cleanTelegramText(domain.replace(/[^\x20-\x7e]/g, ''), 180);
  } catch {
    return '';
  }
}

function createTelegramSilentLogger() {
  return {
    setLevel() {},
    canSend() {
      return false;
    },
    info() {},
    warn() {},
    debug() {},
    error() {},
    log() {}
  };
}

function withTelegramTimeout(operation, timeoutMs = TELEGRAM_CONNECT_TIMEOUT_MS, label = 'Операция Telegram') {
  const ms = Math.max(1000, Math.trunc(Number(timeoutMs || TELEGRAM_CONNECT_TIMEOUT_MS)) || TELEGRAM_CONNECT_TIMEOUT_MS);
  let timeoutId = null;
  const timeoutPromise = new Promise((_, reject) => {
    timeoutId = setTimeout(() => {
      reject(Object.assign(
        new Error(`${label} не ответила за ${Math.round(ms / 1000)} сек.`),
        { code: 'TELEGRAM_TIMEOUT' }
      ));
    }, ms);
  });
  return Promise.race([
    Promise.resolve(operation).finally(() => {
      if (timeoutId) {
        clearTimeout(timeoutId);
      }
    }),
    timeoutPromise
  ]);
}

function parseTelegramProxyUrl(rawValue = '') {
  const raw = cleanTelegramText(rawValue || '', 1200);
  if (!raw) {
    return {
      ok: true,
      proxy: null,
      normalizedProxyUrl: '',
      label: 'Без прокси',
      mode: ''
    };
  }

  let parsed = null;
  try {
    parsed = new URL(raw);
  } catch {
    return {
      ok: false,
      error: 'Укажите прокси в формате tg://proxy?server=...&port=...&secret=...'
    };
  }

  const protocol = String(parsed.protocol || '').toLowerCase();
  const host = String(parsed.hostname || '').toLowerCase();
  const isTelegramProxyLink = (
    (protocol === 'tg:' && host === 'proxy')
    || (
      (protocol === 'https:' || protocol === 'http:')
      && /^(?:t|telegram)\.me$/iu.test(host)
      && /\/proxy\/?$/iu.test(parsed.pathname || '')
    )
  );
  if (!isTelegramProxyLink) {
    return {
      ok: false,
      error: 'Поддерживается MTProto-ссылка Telegram: tg://proxy?server=...&port=...&secret=...'
    };
  }

  const server = cleanTelegramText(
    parsed.searchParams.get('server') || parsed.searchParams.get('host') || '',
    255
  );
  const port = Math.trunc(Number(parsed.searchParams.get('port') || 0) || 0);
  const secret = cleanTelegramText(parsed.searchParams.get('secret') || '', 512).replace(/\s+/gu, '');
  if (!server || port < 1 || port > 65535 || !secret) {
    return {
      ok: false,
      error: 'В ссылке Telegram-прокси должны быть server, port и secret.'
    };
  }
  if (!/^[0-9a-f]+$/iu.test(secret) || secret.length < 32) {
    return {
      ok: false,
      error: 'Secret MTProto-прокси должен быть hex-строкой.'
    };
  }
  const mode = getTelegramProxySecretMode(secret);
  if (mode === 'classic' && secret.length !== 32) {
    return {
      ok: false,
      error: 'Классический MTProxy secret должен содержать ровно 16 байт (32 hex-символа).'
    };
  }
  if (mode === 'random_padding' && secret.length !== 34) {
    return {
      ok: false,
      error: 'MTProxy secret с префиксом dd должен содержать 17 байт (34 hex-символа).'
    };
  }
  if (mode === 'fake_tls' && secret.length <= 34) {
    return {
      ok: false,
      error: 'Fake TLS MTProxy secret с префиксом ee должен содержать домен после ключа.'
    };
  }

  const normalizedProxyUrl = `tg://proxy?server=${encodeURIComponent(server)}&port=${encodeURIComponent(String(port))}&secret=${encodeURIComponent(secret)}`;
  const fakeTlsDomain = mode === 'fake_tls' ? decodeTelegramFakeTlsDomain(secret) : '';
  return {
    ok: true,
    normalizedProxyUrl,
    label: fakeTlsDomain ? `${server}:${port} (${fakeTlsDomain})` : `${server}:${port}`,
    mode,
    fakeTlsDomain,
    proxy: {
      ip: server,
      port,
      MTProxy: true,
      secret,
      timeout: 8
    }
  };
}

function validateTelegramApiSettings(settings = null) {
  const normalized = normalizeTelegramApiSettings(settings);
  if (!normalized.enabled) {
    return { ok: true, settings: normalized };
  }
  if (!normalized.apiId || !normalized.apiHash) {
    return { ok: false, code: 'TELEGRAM_API_CREDENTIALS_MISSING', error: 'Внутренние параметры Telegram API недоступны.' };
  }
  const proxyResult = parseTelegramProxyUrl(normalized.proxyUrl);
  if (!proxyResult.ok) {
    return { ok: false, code: 'TELEGRAM_PROXY_INVALID', error: proxyResult.error };
  }
  return {
    ok: true,
    settings: {
      ...normalized,
      proxyUrl: proxyResult.normalizedProxyUrl || normalized.proxyUrl
    },
    proxy: proxyResult.proxy,
    proxyLabel: proxyResult.label,
    proxyMode: proxyResult.mode || '',
    fakeTlsDomain: proxyResult.fakeTlsDomain || ''
  };
}

function getStoredTelegramSessionString() {
  return cleanTelegramText(authStateStore.get(`${TELEGRAM_AUTH_STORE_KEY}.sessionString`, ''), 20000);
}

function setStoredTelegramSessionString(sessionString = '') {
  const normalized = cleanTelegramText(sessionString || '', 20000);
  if (normalized) {
    authStateStore.set(`${TELEGRAM_AUTH_STORE_KEY}.sessionString`, normalized);
  } else {
    authStateStore.delete(`${TELEGRAM_AUTH_STORE_KEY}.sessionString`);
  }
  return normalized;
}

function shouldUseTelegramWebBridge(settings = null) {
  normalizeTelegramApiSettings(settings);
  return false;
}

function waitForTelegramMs(ms = 0) {
  return new Promise((resolve) => {
    setTimeout(resolve, Math.max(0, Math.trunc(Number(ms || 0)) || 0));
  });
}

function getTelegramDependency() {
  try {
    const telegram = require('telegram');
    const sessions = require('telegram/sessions');
    const uploads = require('telegram/client/uploads');
    const utils = require('telegram/Utils');
    const helpers = require('telegram/Helpers');
    const fakeTlsConnection = require('./telegramFakeTlsConnection');
    if (!telegram?.TelegramClient || !telegram?.Api || !sessions?.StringSession || !uploads?.CustomFile) {
      throw new Error('GramJS exports are unavailable');
    }
    return {
      ok: true,
      TelegramClient: telegram.TelegramClient,
      Api: telegram.Api,
      Utils: utils,
      Helpers: helpers,
      StringSession: sessions.StringSession,
      CustomFile: uploads.CustomFile,
      ConnectionTCPMTProxyFakeTLS: fakeTlsConnection.ConnectionTCPMTProxyFakeTLS,
      ConnectionTCPMTProxyRandomizedIntermediate: fakeTlsConnection.ConnectionTCPMTProxyRandomizedIntermediate
    };
  } catch (error) {
    return {
      ok: false,
      error: error?.message || 'Пакет telegram не установлен.'
    };
  }
}

function buildTelegramClientSignature(settings = null, proxy = null) {
  const normalized = normalizeTelegramApiSettings(settings);
  return JSON.stringify({
    apiId: normalized.apiId,
    apiHash: normalized.apiHash,
    proxy: proxy || null
  });
}

async function disconnectTelegramClient() {
  const client = telegramClient;
  telegramClient = null;
  telegramClientSignature = '';
  telegramPendingAuth = null;
  telegramPendingAuthPromise = null;
  telegramUpdateBridgeInstalledForClient = null;
  if (client && typeof client.disconnect === 'function') {
    try {
      await client.disconnect();
    } catch {
      // ignore disconnect failures
    }
  }
}

function emitTelegramRendererEvent(channel = '', payload = {}) {
  const safeChannel = String(channel || '').trim();
  if (!safeChannel) return false;
  if (!(mainWindow instanceof BrowserWindow) || mainWindow.isDestroyed()) return false;
  try {
    mainWindow.webContents.send(safeChannel, payload && typeof payload === 'object' ? payload : {});
    return true;
  } catch {
    return false;
  }
}

function getTelegramObjectClassName(value = null) {
  if (!value || typeof value !== 'object') return '';
  return cleanTelegramText(
    value.className
    || value._className
    || value._
    || value.constructor?.name
    || '',
    180
  );
}

function normalizeTelegramCallId(value = null) {
  if (value == null) return '';
  if (typeof value === 'bigint') return value.toString();
  if (typeof value === 'number' || typeof value === 'string') {
    return cleanTelegramText(value, 160);
  }
  if (typeof value.toString === 'function') {
    return cleanTelegramText(value.toString(), 160);
  }
  return '';
}

function normalizeTelegramBytes(value = null) {
  if (!value) return Buffer.alloc(0);
  if (Buffer.isBuffer(value)) return Buffer.from(value);
  if (value instanceof Uint8Array) return Buffer.from(value);
  if (value instanceof ArrayBuffer) return Buffer.from(new Uint8Array(value));
  if (Array.isArray(value)) return Buffer.from(value);
  if (typeof value === 'string') {
    return Buffer.from(value, 'binary');
  }
  if (typeof value.toBuffer === 'function') {
    try {
      const buffer = value.toBuffer();
      if (Buffer.isBuffer(buffer) || buffer instanceof Uint8Array) return Buffer.from(buffer);
    } catch {
      return Buffer.alloc(0);
    }
  }
  return Buffer.alloc(0);
}

function bigIntFromBufferBE(buffer = null) {
  const bytes = normalizeTelegramBytes(buffer);
  if (!bytes.length) return 0n;
  return BigInt(`0x${bytes.toString('hex') || '0'}`);
}

function bufferFromBigIntBE(value = 0n, length = 0) {
  let hex = BigInt(value || 0).toString(16);
  if (hex.length % 2) hex = `0${hex}`;
  let buffer = Buffer.from(hex, 'hex');
  if (length > 0) {
    if (buffer.length > length) {
      buffer = buffer.subarray(buffer.length - length);
    } else if (buffer.length < length) {
      buffer = Buffer.concat([Buffer.alloc(length - buffer.length), buffer]);
    }
  }
  return buffer;
}

function modPowBigInt(baseValue = 0n, exponentValue = 0n, modulusValue = 1n) {
  let base = BigInt(baseValue || 0) % BigInt(modulusValue || 1);
  let exponent = BigInt(exponentValue || 0);
  const modulus = BigInt(modulusValue || 1);
  let result = 1n;
  while (exponent > 0n) {
    if (exponent & 1n) {
      result = (result * base) % modulus;
    }
    exponent >>= 1n;
    base = (base * base) % modulus;
  }
  return result;
}

function telegramLongFingerprintFromAuthKey(authKey = null) {
  const hash = crypto.createHash('sha1').update(normalizeTelegramBytes(authKey)).digest();
  const tail = hash.subarray(Math.max(0, hash.length - 8));
  if (tail.length < 8) return 0n;
  return tail.readBigInt64LE(0);
}

function buildTelegramPhoneCallProtocol(ApiClass = null) {
  if (!ApiClass?.PhoneCallProtocol) return null;
  return new ApiClass.PhoneCallProtocol({
    udpP2p: true,
    udpReflector: true,
    minLayer: TELEGRAM_CALL_MIN_LAYER,
    maxLayer: TELEGRAM_CALL_MAX_LAYER,
    libraryVersions: [...TELEGRAM_CALL_LIBRARY_VERSIONS]
  });
}

async function buildTelegramOutgoingCallHandshake(client = null, ApiClass = null) {
  if (!client || !ApiClass?.messages?.GetDhConfig) {
    const fallbackGA = crypto.randomBytes(256);
    return {
      gA: fallbackGA,
      gAHash: crypto.createHash('sha256').update(fallbackGA).digest(),
      exponent: Buffer.alloc(0),
      prime: Buffer.alloc(0),
      generator: 0,
      complete: false
    };
  }

  const dhConfig = await withTelegramTimeout(
    client.invoke(new ApiClass.messages.GetDhConfig({
      version: 0,
      randomLength: 256
    })),
    TELEGRAM_CONNECT_TIMEOUT_MS,
    'Загрузка параметров звонка Telegram'
  );
  const prime = normalizeTelegramBytes(dhConfig?.p || dhConfig?.prime || null);
  const random = normalizeTelegramBytes(dhConfig?.random || null);
  const generator = Math.max(0, Math.trunc(Number(dhConfig?.g || 0) || 0));
  if (!prime.length || !generator) {
    throw Object.assign(new Error('Telegram не вернул DH-параметры для звонка.'), {
      code: 'TELEGRAM_CALL_DH_CONFIG_MISSING'
    });
  }

  const localRandom = crypto.randomBytes(256);
  const exponent = Buffer.alloc(256);
  for (let index = 0; index < exponent.length; index += 1) {
    exponent[index] = localRandom[index] ^ (random[index] || 0);
  }
  const gAValue = modPowBigInt(
    BigInt(generator),
    bigIntFromBufferBE(exponent),
    bigIntFromBufferBE(prime)
  );
  const gA = bufferFromBigIntBE(gAValue, prime.length);
  return {
    gA,
    gAHash: crypto.createHash('sha256').update(gA).digest(),
    exponent,
    prime,
    generator,
    complete: true
  };
}

function rememberTelegramOutgoingCallState(phoneCall = null, handshake = null, settings = null) {
  const callId = normalizeTelegramCallId(phoneCall?.id || phoneCall?.callId || '');
  if (!callId || !handshake?.complete) return false;
  telegramOutgoingCallStateById.set(callId, {
    callId,
    accessHash: normalizeTelegramCallId(phoneCall?.accessHash || ''),
    gA: Buffer.from(handshake.gA || []),
    exponent: Buffer.from(handshake.exponent || []),
    prime: Buffer.from(handshake.prime || []),
    settings: normalizeTelegramApiSettings(settings || {}),
    createdAt: Date.now()
  });
  while (telegramOutgoingCallStateById.size > 20) {
    const oldestKey = telegramOutgoingCallStateById.keys().next().value;
    if (!oldestKey) break;
    telegramOutgoingCallStateById.delete(oldestKey);
  }
  return true;
}

async function maybeConfirmTelegramAcceptedCall(client = null, phoneCall = null, settings = null) {
  if (!client || !phoneCall || typeof phoneCall !== 'object') return false;
  const dependency = getTelegramDependency();
  if (!dependency.ok) return false;
  const callId = normalizeTelegramCallId(phoneCall.id || phoneCall.callId || '');
  const state = telegramOutgoingCallStateById.get(callId) || null;
  if (!state) return false;
  const gB = normalizeTelegramBytes(phoneCall.gB || phoneCall.g_b || phoneCall.g_b_bytes || null);
  if (!gB.length || !state.prime?.length || !state.exponent?.length || !state.gA?.length) return false;
  const authKeyValue = modPowBigInt(
    bigIntFromBufferBE(gB),
    bigIntFromBufferBE(state.exponent),
    bigIntFromBufferBE(state.prime)
  );
  const authKey = bufferFromBigIntBE(authKeyValue, state.prime.length);
  const keyFingerprint = telegramLongFingerprintFromAuthKey(authKey);
  const accessHash = phoneCall.accessHash ?? state.accessHash;
  try {
    await withTelegramTimeout(
      client.invoke(new dependency.Api.phone.ConfirmCall({
        peer: new dependency.Api.InputPhoneCall({
          id: phoneCall.id,
          accessHash
        }),
        gA: state.gA,
        keyFingerprint,
        protocol: buildTelegramPhoneCallProtocol(dependency.Api)
      })),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Подтверждение звонка Telegram'
    );
    telegramOutgoingCallStateById.delete(callId);
    return true;
  } catch (error) {
    return false;
  }
}

function getTelegramPhoneCallReasonKey(reason = null) {
  const className = getTelegramObjectClassName(reason);
  const raw = cleanTelegramText(
    className
    || reason?.reason
    || reason?.type
    || '',
    120
  );
  if (/missed/i.test(raw)) return 'missed';
  if (/busy/i.test(raw)) return 'busy';
  if (/disconnect/i.test(raw)) return 'disconnected';
  if (/hangup|discard|cancel/i.test(raw)) return 'cancelled';
  return raw ? raw.replace(/^PhoneCallDiscardReason/iu, '').toLowerCase() : '';
}

function getTelegramPhoneCallReasonText(reasonKey = '', isOutgoing = false) {
  const normalized = cleanTelegramText(reasonKey || '', 80).toLowerCase();
  if (normalized === 'missed') return isOutgoing ? 'Без ответа' : 'Пропущен';
  if (normalized === 'busy') return 'Занято';
  if (normalized === 'disconnected') return 'Завершён';
  if (normalized === 'cancelled') return 'Отменён';
  return 'Завершён';
}

function buildTelegramPhoneCallActionPresentation(message = null) {
  if (!message || typeof message !== 'object') return null;
  const action = message.action || message.messageAction || message._action || null;
  if (!action || typeof action !== 'object') return null;
  const actionClass = getTelegramObjectClassName(action);
  if (!/MessageActionPhoneCall/i.test(actionClass) && !action.callId) return null;

  const isOutgoing = message.out === true || message.isMine === true || message.outgoing === true;
  const reasonKey = getTelegramPhoneCallReasonKey(action.reason || action.discardReason || null);
  const durationSeconds = Math.max(0, Math.trunc(Number(action.duration || action.durationSeconds || 0) || 0));
  const title = action.video === true
    ? (isOutgoing ? 'Исходящий видеозвонок' : 'Входящий видеозвонок')
    : (isOutgoing ? 'Исходящий звонок' : 'Входящий звонок');
  const statusText = reasonKey
    ? getTelegramPhoneCallReasonText(reasonKey, isOutgoing)
    : (durationSeconds > 0 ? 'Завершён' : 'Звонок');
  const text = cleanTelegramMultiline(
    [title, statusText].filter(Boolean).join('\n'),
    6000
  );
  return {
    title,
    statusText,
    text,
    formattedText: text,
    attachmentLabel: 'Звонок',
    systemSignal: 'telegram_phone_call',
    callId: normalizeTelegramCallId(action.callId || action.id || ''),
    reason: reasonKey,
    durationSeconds,
    video: action.video === true,
    outgoing: isOutgoing
  };
}

function getTelegramPhoneCallStatusFromClassName(className = '') {
  const normalized = cleanTelegramText(className || '', 160);
  if (/Requested/i.test(normalized)) return 'requested';
  if (/Waiting/i.test(normalized)) return 'waiting';
  if (/Accepted/i.test(normalized)) return 'accepted';
  if (/Discarded/i.test(normalized)) return 'discarded';
  if (/PhoneCall\b/i.test(normalized)) return 'active';
  return '';
}

function getTelegramPhoneCallRemotePeerId(phoneCall = null) {
  if (!phoneCall || typeof phoneCall !== 'object') return '';
  const className = getTelegramObjectClassName(phoneCall);
  const adminId = normalizeTelegramPeerId(phoneCall.adminId || phoneCall.admin_id || '');
  const participantId = normalizeTelegramPeerId(phoneCall.participantId || phoneCall.participant_id || '');
  if (/Requested/i.test(className) && adminId) return adminId;
  return participantId || adminId;
}

function serializeTelegramPhoneCallUpdate(update = null, settings = null) {
  if (!update || typeof update !== 'object') return null;
  const updateClass = getTelegramObjectClassName(update);
  const phoneCall = update.phoneCall || update.call || (/PhoneCall/i.test(updateClass) ? update : null);
  if (!phoneCall || typeof phoneCall !== 'object') return null;
  const phoneCallClass = getTelegramObjectClassName(phoneCall);
  if (!/PhoneCall/i.test(updateClass) && !/PhoneCall/i.test(phoneCallClass)) return null;
  const remotePeerId = getTelegramPhoneCallRemotePeerId(phoneCall);
  const reason = getTelegramPhoneCallReasonKey(phoneCall.reason || phoneCall.discardReason || null);
  const status = getTelegramPhoneCallStatusFromClassName(phoneCallClass || updateClass);
  return {
    source: 'telegram',
    updateClass,
    callClass: phoneCallClass,
    status,
    incoming: status === 'requested',
    ended: status === 'discarded',
    accepted: status === 'accepted' || status === 'active',
    callId: normalizeTelegramCallId(phoneCall.id || phoneCall.callId || ''),
    accessHash: normalizeTelegramCallId(phoneCall.accessHash || ''),
    adminId: normalizeTelegramPeerId(phoneCall.adminId || ''),
    participantId: normalizeTelegramPeerId(phoneCall.participantId || ''),
    peerId: remotePeerId,
    chatId: remotePeerId ? normalizeTelegramChatId(remotePeerId) : '',
    memberId: remotePeerId ? `telegram:${remotePeerId}` : '',
    reason,
    durationSeconds: Math.max(0, Math.trunc(Number(phoneCall.duration || phoneCall.durationSeconds || 0) || 0)),
    video: phoneCall.video === true,
    settingsFingerprint: settings ? buildTelegramClientSignature(settings, null) : '',
    receivedAt: Date.now()
  };
}

function getTelegramMessagePeerId(message = null) {
  if (!message || typeof message !== 'object') return '';
  return normalizeTelegramPeerId(
    message.peerId?.userId
    || message.peerId?.channelId
    || message.peerId?.chatId
    || message.peer?.userId
    || message.peer?.channelId
    || message.peer?.chatId
    || message.chatId
    || message.toId?.userId
    || message.toId?.channelId
    || message.toId?.chatId
    || getTelegramSenderId(message)
    || ''
  );
}

function serializeTelegramMessageUpdate(update = null) {
  if (!update || typeof update !== 'object') return null;
  const updateClass = getTelegramObjectClassName(update);
  const message = update.message && typeof update.message === 'object' ? update.message : null;
  let peerId = '';
  let messageId = '';
  let isCallService = false;
  if (message) {
    peerId = getTelegramMessagePeerId(message);
    messageId = getTelegramMessageId(message);
    isCallService = Boolean(buildTelegramPhoneCallActionPresentation(message));
  } else if (/UpdateShortMessage/i.test(updateClass)) {
    peerId = normalizeTelegramPeerId(update.userId || update.user_id || '');
    messageId = cleanTelegramText(update.id || '', 80);
  } else if (/UpdateShortChatMessage/i.test(updateClass)) {
    peerId = normalizeTelegramPeerId(update.chatId || update.chat_id || '');
    messageId = cleanTelegramText(update.id || '', 80);
  }
  if (!peerId && !messageId && !/Message/i.test(updateClass)) return null;
  return {
    source: 'telegram',
    type: 'message',
    updateClass,
    peerId,
    chatId: peerId ? normalizeTelegramChatId(peerId) : '',
    messageId,
    isCallService,
    receivedAt: Date.now()
  };
}

function getTelegramPeerIdFromUpdatePeer(peer = null, update = null) {
  return normalizeTelegramPeerId(
    peer?.userId
    || peer?.user_id
    || peer?.channelId
    || peer?.channel_id
    || peer?.chatId
    || peer?.chat_id
    || update?.userId
    || update?.user_id
    || update?.channelId
    || update?.channel_id
    || update?.chatId
    || update?.chat_id
    || ''
  );
}

function serializeTelegramReadStateUpdate(update = null) {
  if (!update || typeof update !== 'object') return null;
  const updateClass = getTelegramObjectClassName(update);
  if (!/UpdateRead/i.test(updateClass)) return null;
  const peerId = getTelegramPeerIdFromUpdatePeer(update.peer || update.dialogPeer || null, update);
  const maxId = Math.max(0, Math.trunc(Number(update.maxId || update.max_id || update.readMaxId || update.read_max_id || 0) || 0));
  if (!peerId && !maxId) return null;
  return {
    source: 'telegram',
    type: /Outbox/i.test(updateClass) ? 'read_outbox' : 'read_inbox',
    updateClass,
    peerId,
    chatId: peerId ? normalizeTelegramChatId(peerId) : '',
    maxId,
    isReadReceipt: /Outbox/i.test(updateClass),
    receivedAt: Date.now()
  };
}

function handleTelegramClientUpdate(update = null, settings = null, client = telegramClient) {
  try {
    const phoneCallUpdate = serializeTelegramPhoneCallUpdate(update, settings);
    if (phoneCallUpdate) {
      const updateClass = getTelegramObjectClassName(update);
      const phoneCall = update?.phoneCall || update?.call || (/PhoneCall/i.test(updateClass) ? update : null);
      if (phoneCallUpdate.accepted === true) {
        const acceptedCallId = normalizeTelegramCallId(phoneCall?.id || phoneCall?.callId || phoneCallUpdate.callId || '');
        if (acceptedCallId && telegramOutgoingCallStateById.has(acceptedCallId)) {
          void maybeConfirmTelegramAcceptedCall(client, phoneCall, settings).then((confirmed) => {
            emitTelegramRendererEvent('yuchat-telegram-phone-call-update', {
              ...phoneCallUpdate,
              accepted: false,
              status: confirmed ? 'confirmed' : 'confirm_failed',
              confirmed: confirmed === true,
              mediaPending: confirmed === true,
              error: confirmed ? '' : 'Не удалось подтвердить звонок Telegram.'
            });
          }).catch(() => {
            emitTelegramRendererEvent('yuchat-telegram-phone-call-update', {
              ...phoneCallUpdate,
              accepted: false,
              status: 'confirm_failed',
              confirmed: false,
              mediaPending: false,
              error: 'Не удалось подтвердить звонок Telegram.'
            });
          });
        }
      } else if (phoneCallUpdate.ended === true && phoneCallUpdate.callId) {
        telegramOutgoingCallStateById.delete(phoneCallUpdate.callId);
      }
      emitTelegramRendererEvent('yuchat-telegram-phone-call-update', phoneCallUpdate);
      emitTelegramRendererEvent('yuchat-telegram-update', {
        ...phoneCallUpdate,
        type: 'phone_call',
        isCallService: true
      });
      return;
    }
    const messageUpdate = serializeTelegramMessageUpdate(update);
    if (messageUpdate) {
      emitTelegramRendererEvent('yuchat-telegram-update', messageUpdate);
      return;
    }
    const readStateUpdate = serializeTelegramReadStateUpdate(update);
    if (readStateUpdate) {
      emitTelegramRendererEvent('yuchat-telegram-update', readStateUpdate);
    }
  } catch {
    // Telegram update payloads vary between layers; ignore bridge serialization failures.
  }
}

function installTelegramClientUpdateBridge(client = null, settings = null) {
  if (!client || typeof client.addEventHandler !== 'function') return false;
  if (telegramUpdateBridgeInstalledForClient === client || client.__yuChatUpdateBridgeInstalled === true) return true;
  try {
    client.addEventHandler((update) => {
      handleTelegramClientUpdate(update, settings, client);
    });
    Object.defineProperty(client, '__yuChatUpdateBridgeInstalled', {
      value: true,
      enumerable: false,
      configurable: false
    });
    telegramUpdateBridgeInstalledForClient = client;
    return true;
  } catch {
    return false;
  }
}

async function ensureTelegramClient(rawSettings = null, options = {}) {
  const validation = validateTelegramApiSettings(rawSettings);
  if (!validation.ok) {
    throw Object.assign(new Error(validation.error), {
      code: validation.code || 'TELEGRAM_SETTINGS_INVALID'
    });
  }
  const dependency = getTelegramDependency();
  if (!dependency.ok) {
    throw Object.assign(new Error(`GramJS недоступен: ${dependency.error}`), {
      code: 'TELEGRAM_DEPENDENCY_MISSING'
    });
  }

  const settings = validation.settings;
  const signature = buildTelegramClientSignature(settings, validation.proxy);
  const ignoreStoredSession = options?.ignoreStoredSession === true;
  if (!ignoreStoredSession && telegramClient && telegramClientSignature === signature) {
    installTelegramClientUpdateBridge(telegramClient, settings);
    return {
      client: telegramClient,
      settings,
      proxyLabel: validation.proxyLabel,
      proxyMode: validation.proxyMode || '',
      fakeTlsDomain: validation.fakeTlsDomain || ''
    };
  }

  await disconnectTelegramClient();
  const sessionString = ignoreStoredSession ? '' : getStoredTelegramSessionString();
  const stringSession = new dependency.StringSession(sessionString || '');
  const clientOptions = {
    connectionRetries: 3,
    requestRetries: 2,
    useWSS: false,
    deviceModel: TELEGRAM_WEB_A_DEVICE_MODEL,
    systemVersion: TELEGRAM_WEB_A_SYSTEM_VERSION,
    appVersion: TELEGRAM_WEB_A_APP_VERSION,
    langCode: 'ru',
    systemLangCode: 'ru-RU',
    baseLogger: createTelegramSilentLogger()
  };
  if (validation.proxy) {
    if (validation.proxyMode === 'fake_tls') {
      clientOptions.connection = dependency.ConnectionTCPMTProxyFakeTLS;
      clientOptions.proxy = {
        ip: validation.proxy.ip,
        port: validation.proxy.port,
        secret: validation.proxy.secret,
        timeout: validation.proxy.timeout || 8,
        fakeTls: true
      };
    } else if (validation.proxyMode === 'random_padding') {
      clientOptions.connection = dependency.ConnectionTCPMTProxyRandomizedIntermediate;
      clientOptions.proxy = validation.proxy;
    } else {
      clientOptions.proxy = validation.proxy;
    }
  }
  const client = new dependency.TelegramClient(
    stringSession,
    settings.apiId,
    settings.apiHash,
    clientOptions
  );
  if (typeof client.setLogLevel === 'function') {
    client.setLogLevel('none');
  }
  try {
    const connected = await withTelegramTimeout(
      client.connect(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      validation.proxy ? `Подключение Telegram через ${validation.proxyLabel}` : 'Подключение Telegram'
    );
    if (connected !== true && !isTelegramClientTransportReady(client)) {
      throw Object.assign(new Error(
        validation.proxy
          ? 'Telegram-прокси открыл соединение, но MTProto-ключ авторизации не создался. Код в Telegram в этом состоянии не отправляется.'
          : 'Telegram не смог создать MTProto-ключ авторизации.'
      ), {
        code: 'TELEGRAM_CONNECT_FAILED'
      });
    }
  } catch (error) {
    try {
      if (typeof client.disconnect === 'function') {
        await client.disconnect();
      }
    } catch {
      // ignore cleanup failures
    }
    throw error;
  }
  telegramClient = client;
  telegramClientSignature = signature;
  installTelegramClientUpdateBridge(client, settings);
  return {
    client,
    settings,
    proxyLabel: validation.proxyLabel,
    proxyMode: validation.proxyMode || '',
    fakeTlsDomain: validation.fakeTlsDomain || ''
  };
}

function saveTelegramClientSession(client = telegramClient) {
  if (!client?.session || typeof client.session.save !== 'function') {
    return '';
  }
  try {
    return setStoredTelegramSessionString(client.session.save());
  } catch {
    return '';
  }
}

function isTelegramClientTransportReady(client = null) {
  if (!client || typeof client !== 'object') return false;
  if (client._sender?._userConnected === true || client._sender?._finishedConnecting === true) return true;
  if (typeof client._sender?.isConnected === 'function' && client._sender.isConnected() === true) return true;
  try {
    return Boolean(client.session?.getAuthKey?.()?.getKey?.());
  } catch {
    return false;
  }
}

function normalizeTelegramPeerId(value = null) {
  if (value == null) return '';
  if (typeof value === 'string' || typeof value === 'number') {
    return cleanTelegramText(value, 120);
  }
  if (typeof value === 'bigint') {
    return value.toString();
  }
  if (typeof value.toString === 'function') {
    return cleanTelegramText(value.toString(), 120);
  }
  return '';
}

function normalizeTelegramStatus(entity = null) {
  const status = entity?.status && typeof entity.status === 'object' ? entity.status : null;
  if (!status) return { text: '', presence: null, kind: '' };
  const className = cleanTelegramText(status.className || status.constructor?.name || '', 120);
  const timestamp = Number(status.wasOnline || status.date || status.expires || 0);
  const timestampMs = timestamp > 0
    ? (timestamp < 10_000_000_000 ? timestamp * 1000 : timestamp)
    : 0;
  const isOnline = /Online/iu.test(className) && !/Offline/iu.test(className);
  const isRecently = /Recently/iu.test(className);
  const isLastWeek = /LastWeek/iu.test(className);
  const isLastMonth = /LastMonth/iu.test(className);
  const isOffline = /Offline/iu.test(className);
  const formatLastSeen = (timestampValue = 0) => {
    if (!timestampValue) return '';
    const date = new Date(timestampValue);
    if (Number.isNaN(date.getTime())) return '';
    const pad = (value) => String(value).padStart(2, '0');
    const time = `${pad(date.getHours())}:${pad(date.getMinutes())}`;
    const today = new Date();
    const startOfToday = new Date(today.getFullYear(), today.getMonth(), today.getDate()).getTime();
    const startOfDate = new Date(date.getFullYear(), date.getMonth(), date.getDate()).getTime();
    const dayDiff = Math.round((startOfToday - startOfDate) / 86400000);
    if (dayDiff === 0) return `был(а) сегодня в ${time}`;
    if (dayDiff === 1) return `был(а) вчера в ${time}`;
    return `был(а) ${pad(date.getDate())}.${pad(date.getMonth() + 1)}.${date.getFullYear()} в ${time}`;
  };
  const text = isOnline
    ? 'в сети'
    : isRecently
      ? 'был(а) недавно'
      : isLastWeek
        ? 'был(а) на этой неделе'
        : isLastMonth
          ? 'был(а) в этом месяце'
          : (isOffline ? formatLastSeen(timestampMs) : '');
  return {
    text,
    kind: className,
    presence: (isOnline || isOffline) ? {
      isOnline,
      onlineKind: isOnline ? 'ONLINE' : 'OFFLINE',
      customKind: '',
      lastSeenAt: isOffline ? timestampMs : 0
    } : null
  };
}

function normalizeTelegramEpochSeconds(value = 0) {
  if (value == null) return 0;
  if (typeof value === 'bigint') {
    const numeric = Number(value);
    return Number.isFinite(numeric) ? Math.max(0, Math.round(numeric)) : 0;
  }
  if (typeof value === 'number') {
    return Number.isFinite(value) ? Math.max(0, Math.round(value > 10_000_000_000 ? value / 1000 : value)) : 0;
  }
  const numeric = Number(String(value || '').trim());
  if (!Number.isFinite(numeric)) return 0;
  return Math.max(0, Math.round(numeric > 10_000_000_000 ? numeric / 1000 : numeric));
}

function getTelegramDialogNotifySettings(dialog = null) {
  return [
    dialog?.notifySettings,
    dialog?.notificationSettings,
    dialog?.notify_settings,
    dialog?.dialog?.notifySettings,
    dialog?.dialog?.notify_settings,
    dialog?.entity?.notifySettings,
    dialog?.entity?.notify_settings
  ].find((candidate) => candidate && typeof candidate === 'object') || {};
}

function normalizeTelegramNotifySettings(dialog = null) {
  const settings = getTelegramDialogNotifySettings(dialog);
  const rawMuteUntil = settings.muteUntil ?? settings.mute_until ?? settings.mutedUntil ?? settings.muted_until ?? 0;
  const muteUntil = normalizeTelegramEpochSeconds(rawMuteUntil);
  const nowSeconds = Math.floor(Date.now() / 1000);
  const isMuted = Boolean(
    settings.isMuted === true
    || settings.muted === true
    || (muteUntil > nowSeconds)
  );
  return {
    isMuted,
    muteUntil: Math.max(0, muteUntil),
    rule: isMuted ? 'MUTED' : 'DEFAULT'
  };
}

function isTelegramDialogPinned(dialog = null) {
  return Boolean(
    dialog?.pinned === true
    || dialog?.isPinned === true
    || dialog?.pinnedToTop === true
    || dialog?.dialog?.pinned === true
    || dialog?.dialog?.isPinned === true
  );
}

function normalizeTelegramDialogPinnedAt(dialog = null) {
  return isTelegramDialogPinned(dialog) ? TELEGRAM_DIALOG_PINNED_AT : '';
}

function isTelegramDialogArchived(dialog = null, options = {}) {
  if (options?.archived === true) return true;
  const folderId = Number(
    dialog?.folderId
    ?? dialog?.folder?.id
    ?? dialog?._folderId
    ?? dialog?.dialog?.folderId
    ?? 0
  );
  return dialog?.archived === true || folderId === 1;
}

function normalizeTelegramDialog(dialog = null, settings = null, options = {}) {
  if (!dialog || typeof dialog !== 'object') return null;
  const id = normalizeTelegramPeerId(dialog.id || dialog.entity?.id || dialog.inputEntity?.userId || dialog.inputEntity?.channelId || dialog.inputEntity?.chatId);
  if (!id) return null;
  const title = cleanTelegramText(
    dialog.title
    || dialog.name
    || [dialog.entity?.firstName, dialog.entity?.lastName].filter(Boolean).join(' ')
    || dialog.entity?.username
    || `Telegram ${id}`,
    180
  ) || `Telegram ${id}`;
  const rawDate = Number(dialog.date || dialog.message?.date || 0);
  const timestamp = rawDate > 0
    ? (rawDate < 10_000_000_000 ? rawDate * 1000 : rawDate)
    : Date.now();
  const rawMessage = dialog.message && typeof dialog.message === 'object' ? dialog.message : null;
  const phoneCallPreview = buildTelegramPhoneCallActionPresentation(rawMessage);
  const messageText = cleanTelegramText(
    phoneCallPreview?.text
    || rawMessage?.message
    || rawMessage?.text
    || '',
    420
  );
  const previewMessageId = cleanTelegramText(
    rawMessage?.id
    ?? rawMessage?.messageId
    ?? rawMessage?._id
    ?? '',
    120
  );
  const previewIsMine = rawMessage?.out === true || rawMessage?.isMine === true;
  const readInboxMaxId = Math.max(0, Math.trunc(Number(
    dialog.readInboxMaxId
    ?? dialog.read_inbox_max_id
    ?? dialog.dialog?.readInboxMaxId
    ?? dialog.dialog?.read_inbox_max_id
    ?? 0
  ) || 0));
  const readOutboxMaxId = Math.max(0, Math.trunc(Number(
    dialog.readOutboxMaxId
    ?? dialog.read_outbox_max_id
    ?? dialog.dialog?.readOutboxMaxId
    ?? dialog.dialog?.read_outbox_max_id
    ?? 0
  ) || 0));
  const previewMessageNumericId = Math.max(0, Math.trunc(Number(previewMessageId || 0) || 0));
  const previewDeliveryStatus = previewIsMine
    ? (readOutboxMaxId > 0 && previewMessageNumericId > 0 && previewMessageNumericId <= readOutboxMaxId ? 'read' : 'sent')
    : '';
  const previewReactions = normalizeTelegramMessageReactions(rawMessage);
  const unreadMentionsCount = Math.max(0, Math.trunc(Number(
    dialog.unreadMentionsCount
    ?? dialog.unreadMentionCount
    ?? dialog.unread_mentions_count
    ?? dialog.dialog?.unreadMentionsCount
    ?? dialog.dialog?.unreadMentionCount
    ?? dialog.dialog?.unread_mentions_count
    ?? 0
  ) || 0));
  const unreadReactionsCount = Math.max(0, Math.trunc(Number(
    dialog.unreadReactionsCount
    ?? dialog.unreadReactionCount
    ?? dialog.unread_reactions_count
    ?? dialog.dialog?.unreadReactionsCount
    ?? dialog.dialog?.unreadReactionCount
    ?? dialog.dialog?.unread_reactions_count
    ?? 0
  ) || 0));
  const isMegagroup = dialog.entity?.megagroup === true || dialog.megagroup === true;
  const type = dialog.isUser
    ? 'direct'
    : ((dialog.isGroup || isMegagroup) ? 'group' : (dialog.isChannel ? 'channel' : 'chat'));
  const previewAuthor = getTelegramMessageAuthor(rawMessage);
  const shouldShowPreviewAuthor = Boolean(
    rawMessage
    && !previewIsMine
    && type !== 'direct'
    && isMeaningfulTelegramPreviewAuthorName(previewAuthor.name, getTelegramSenderId(rawMessage))
  );
  const username = cleanTelegramText(dialog.entity?.username || '', 120);
  const phone = cleanTelegramText(dialog.entity?.phone || '', 80);
  const about = cleanTelegramText(dialog.entity?.about || dialog.entity?.bio || '', 2400);
  const birthday = normalizeTelegramBirthdayValue(dialog.entity?.birthday || null);
  const directMemberId = type === 'direct' ? `telegram:${id}` : '';
  const status = normalizeTelegramStatus(dialog.entity || null);
  const notifySettings = normalizeTelegramNotifySettings(dialog);
  const isPinned = isTelegramDialogPinned(dialog);
  const pinnedAt = normalizeTelegramDialogPinnedAt(dialog);
  const avatarCacheKey = buildTelegramAvatarCacheKey(dialog.entity || null, id);
  const avatarResourceUrl = rememberTelegramAvatarRecord(dialog.entity || null, id, settings, dialog.inputEntity || null);
  const cachedAvatarUrl = getCachedTelegramAvatarDataUrl(avatarCacheKey);
  const avatarUrl = cachedAvatarUrl || avatarResourceUrl;
  const profileDetails = {
    username,
    phone,
    about,
    bio: about,
    birthday
  };

  return {
    id,
    chatId: `tg:${id}`,
    title,
    type,
    telegramType: type,
    memberId: directMemberId,
    directMemberId,
    username,
    phone,
    about,
    bio: about,
    birthday,
    details: profileDetails,
    profile: directMemberId ? {
      id: directMemberId,
      memberId: directMemberId,
      peerId: id,
      fullName: title,
      displayName: title,
      name: title,
      label: title,
      title,
      username,
      phone,
      about,
      bio: about,
      birthday,
      avatarUrl,
      photoUrl: avatarUrl,
      details: profileDetails
    } : null,
    statusText: cleanTelegramText(status.text || '', 120),
    statusKind: cleanTelegramText(status.kind || '', 120),
    presence: status.presence,
    notifySettings,
    isMuted: notifySettings.isMuted === true,
    pinned: isPinned,
    pinnedAt,
    isBot: dialog.entity?.bot === true,
    isArchived: isTelegramDialogArchived(dialog, options),
    avatarUrl,
    avatarCacheKey,
    avatarResourceUrl,
    unreadCount: Math.max(0, Math.trunc(Number(dialog.unreadCount || 0) || 0)),
    unreadMentionsCount,
    unreadReactionsCount,
    mentionedMe: unreadMentionsCount > 0,
    reactionOnMine: unreadReactionsCount > 0,
    readInboxMaxId,
    readOutboxMaxId,
    previewText: messageText || (dialog.message ? 'Вложение или сервисное сообщение' : 'Сообщений пока нет'),
    previewMessageId,
    previewIsMine,
    previewDeliveryStatus,
    previewReactions,
    previewAttachment: phoneCallPreview?.attachmentLabel || '',
    previewIsSystem: Boolean(phoneCallPreview),
    previewAuthor: shouldShowPreviewAuthor ? cleanTelegramText(previewAuthor.name || '', 160) : '',
    previewAuthorMemberId: shouldShowPreviewAuthor ? cleanTelegramText(previewAuthor.memberId || '', 160) : '',
    previewAuthorAvatarUrl: '',
    previewAuthorAvatarResourceUrl: '',
    previewTimestamp: timestamp,
    updatedAt: timestamp
  };
}

function rememberTelegramEntity(key = '', entity = null) {
  const normalizedKey = cleanTelegramText(key || '', 260);
  if (!normalizedKey || !entity) return;
  telegramEntityCacheByKey.set(normalizedKey, entity);
}

function rememberTelegramDialogEntity(dialog = null, normalizedDialog = null) {
  if (!dialog || typeof dialog !== 'object' || !normalizedDialog) return;
  const entity = dialog.inputEntity || dialog.entity || null;
  const keys = [
    normalizedDialog.chatId,
    normalizedDialog.id,
    normalizedDialog.username ? `@${normalizedDialog.username}` : ''
  ].filter(Boolean);
  keys.forEach((key) => rememberTelegramEntity(key, entity || normalizedDialog.id));
}

function normalizeTelegramChatId(value = '') {
  const raw = cleanTelegramText(value || '', 260);
  if (!raw) return '';
  return raw.startsWith(TELEGRAM_DIALOG_PREFIX) ? raw : `${TELEGRAM_DIALOG_PREFIX}${raw}`;
}

function getTelegramPeerIdFromChatId(chatId = '') {
  const normalized = cleanTelegramText(chatId || '', 260);
  if (!normalized) return '';
  if (!normalized.startsWith(TELEGRAM_DIALOG_PREFIX)) return normalized;
  if (normalized.startsWith('tg:web:')) return '';
  return cleanTelegramText(normalized.slice(TELEGRAM_DIALOG_PREFIX.length), 220);
}

function normalizeTelegramNumericId(value = null) {
  const raw = normalizeTelegramPeerId(value);
  if (!raw) return 0;
  const numeric = Number(raw);
  return Number.isSafeInteger(numeric) ? numeric : 0;
}

async function resolveTelegramEntity(client = null, chatId = '', peerHint = '') {
  const peerId = cleanTelegramText(peerHint || getTelegramPeerIdFromChatId(chatId), 220);
  if (!client || !peerId) {
    throw Object.assign(new Error('Не удалось определить Telegram-диалог.'), {
      code: 'TELEGRAM_PEER_MISSING'
    });
  }
  const cacheKeys = [
    normalizeTelegramChatId(peerId),
    chatId,
    peerId
  ].filter(Boolean);
  for (const key of cacheKeys) {
    if (telegramEntityCacheByKey.has(key)) {
      return telegramEntityCacheByKey.get(key);
    }
  }
  const candidates = [];
  candidates.push(peerId);
  const numeric = Number(peerId);
  if (Number.isSafeInteger(numeric)) {
    candidates.push(numeric);
  }
  if (/^-?\d+$/u.test(peerId)) {
    try {
      candidates.push(BigInt(peerId));
    } catch {
      // BigInt may be unavailable in very old runtimes; string/number candidates remain.
    }
  }
  let lastError = null;
  for (const candidate of candidates) {
    try {
      const entity = await client.getEntity(candidate);
      if (entity) {
        cacheKeys.forEach((key) => rememberTelegramEntity(key, entity));
        return entity;
      }
    } catch (error) {
      lastError = error;
    }
  }
  throw Object.assign(new Error(lastError?.message || 'Telegram-диалог не найден.'), {
    code: 'TELEGRAM_PEER_NOT_FOUND'
  });
}

async function hydrateTelegramDialogPeerState(pairs = [], client = null) {
  const sourcePairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => pair?.normalized && pair?.dialog && client)
    .slice(0, 180);
  if (!sourcePairs.length || !client) return;
  const dependency = getTelegramDependency();
  if (!dependency.ok || !dependency.Api?.messages?.GetPeerDialogs || !dependency.Api?.InputDialogPeer) return;

  const inputPairs = [];
  for (const pair of sourcePairs) {
    try {
      const entity = pair.dialog?.inputEntity || pair.dialog?.entity || null;
      const inputPeer = typeof client.getInputEntity === 'function'
        ? await client.getInputEntity(entity || pair.normalized.id).catch(() => entity)
        : entity;
      if (!inputPeer) continue;
      inputPairs.push({
        pair,
        inputDialogPeer: new dependency.Api.InputDialogPeer({ peer: inputPeer })
      });
    } catch {
      // Dialog state hydration is best-effort; the main getDialogs payload remains usable.
    }
  }
  if (!inputPairs.length) return;

  const chunkSize = 80;
  for (let offset = 0; offset < inputPairs.length; offset += chunkSize) {
    const chunk = inputPairs.slice(offset, offset + chunkSize);
    try {
      const response = await withTelegramTimeout(
        client.invoke(new dependency.Api.messages.GetPeerDialogs({
          peers: chunk.map((item) => item.inputDialogPeer)
        })),
        TELEGRAM_PROFILE_TIMEOUT_MS,
        'Загрузка состояния диалогов Telegram'
      );
      const dialogs = Array.isArray(response?.dialogs) ? response.dialogs : [];
      const dialogByPeerId = new Map();
      dialogs.forEach((apiDialog) => {
        const peerId = normalizeTelegramPeerId(
          dependency.Utils?.getPeerId
            ? dependency.Utils.getPeerId(apiDialog?.peer)
            : ''
        );
        if (peerId) dialogByPeerId.set(peerId, apiDialog);
      });

      chunk.forEach((item, index) => {
        const normalized = item.pair?.normalized;
        if (!normalized) return;
        const apiDialog = dialogByPeerId.get(normalized.id) || dialogs[index] || null;
        if (!apiDialog) return;
        const notifySettings = normalizeTelegramNotifySettings({
          notifySettings: apiDialog.notifySettings,
          dialog: apiDialog
        });
        const isPinned = isTelegramDialogPinned(apiDialog);
        normalized.notifySettings = notifySettings;
        normalized.isMuted = notifySettings.isMuted === true;
        normalized.pinned = isPinned;
        normalized.pinnedAt = normalizeTelegramDialogPinnedAt(apiDialog);
      });
    } catch {
      // Keep the original getDialogs state if the batch refresh is unavailable.
    }
  }
}

function getTelegramMessageId(message = null) {
  return cleanTelegramText(message?.id ?? message?.messageId ?? '', 80);
}

function getTelegramMessageTimestamp(message = null) {
  const rawDate = Number(message?.date || message?.createdAt || message?.timestamp || 0);
  return rawDate > 0
    ? (rawDate < 10_000_000_000 ? rawDate * 1000 : rawDate)
    : Date.now();
}

function getTelegramEntityDisplayName(entity = null, fallback = '') {
  return cleanTelegramText(
    entity?.title
    || [entity?.firstName, entity?.lastName].filter(Boolean).join(' ')
    || entity?.username
    || entity?.phone
    || fallback
    || '',
    160
  );
}

function getTelegramSenderId(message = null) {
  return normalizeTelegramPeerId(
    message?.senderId
    || message?.fromId?.userId
    || message?.fromId?.channelId
    || message?.fromId?.chatId
    || message?.sender?.id
    || ''
  );
}

function getTelegramMessageSenderEntity(message = null) {
  if (!message || typeof message !== 'object') return null;
  return (
    message.sender
    || message._sender
    || message.from
    || message.fromEntity
    || null
  );
}

function isMeaningfulTelegramPreviewAuthorName(name = '', senderId = '') {
  const cleaned = cleanTelegramText(name || '', 160);
  if (!cleaned) return false;
  const normalized = cleaned.toLowerCase();
  const normalizedCompact = normalized.replace(/\s+/g, ' ').trim();
  const normalizedSenderFallback = senderId
    ? cleanTelegramText(`Telegram ${senderId}`, 180).toLowerCase()
    : '';
  if (/^(telegram|телеграм|tg)(?:\s+(?:канал|channel|группа|group|чат|chat|бот|bot))?$/iu.test(normalizedCompact)) {
    return false;
  }
  return normalized !== 'telegram' && (!normalizedSenderFallback || normalized !== normalizedSenderFallback);
}

function getTelegramMessageAuthor(message = null, senderEntity = null) {
  const isMine = message?.out === true || message?.isMine === true || message?.outgoing === true;
  if (isMine) {
    return {
      name: 'Вы',
      memberId: 'telegram:self'
    };
  }
  const senderId = getTelegramSenderId(message);
  const senderName = getTelegramEntityDisplayName(senderEntity || getTelegramMessageSenderEntity(message), message?.postAuthor || '');
  return {
    name: senderName || (senderId ? `Telegram ${senderId}` : 'Telegram'),
    memberId: senderId ? `telegram:${senderId}` : ''
  };
}

async function resolveTelegramSenderEntity(client = null, message = null) {
  const embeddedEntity = getTelegramMessageSenderEntity(message);
  if (embeddedEntity && typeof embeddedEntity === 'object') return embeddedEntity;
  const senderId = getTelegramSenderId(message);
  if (!client || !senderId) return null;
  const cacheKeys = [
    `telegram:${senderId}`,
    normalizeTelegramChatId(senderId),
    senderId
  ].filter(Boolean);
  for (const key of cacheKeys) {
    if (telegramEntityCacheByKey.has(key)) {
      return telegramEntityCacheByKey.get(key);
    }
  }
  return await resolveTelegramEntity(client, '', senderId);
}

function normalizeTelegramBirthdayValue(value = null) {
  if (!value || typeof value !== 'object') return '';
  const day = Math.trunc(Number(value.day || 0) || 0);
  const month = Math.trunc(Number(value.month || 0) || 0);
  const year = Math.trunc(Number(value.year || 0) || 0);
  if (day < 1 || day > 31 || month < 1 || month > 12) return '';
  const dayPart = String(day).padStart(2, '0');
  const monthPart = String(month).padStart(2, '0');
  if (year > 0) {
    return `${String(year).padStart(4, '0')}-${monthPart}-${dayPart}`;
  }
  return `${dayPart}.${monthPart}`;
}

function getTelegramResultUsers(result = null) {
  const users = Array.isArray(result?.users)
    ? result.users
    : (Array.isArray(result?.user) ? result.user : []);
  return users.filter((user) => user && typeof user === 'object');
}

function getTelegramFullUserObject(result = null) {
  if (!result || typeof result !== 'object') return null;
  return (
    result.fullUser
    || result.full_user
    || result.userFull
    || result.UserFull
    || null
  );
}

function extractTelegramFullUserDetails(result = null, fallbackEntity = null) {
  const fullUser = getTelegramFullUserObject(result);
  const users = getTelegramResultUsers(result);
  const fullUserId = normalizeTelegramPeerId(fullUser?.id || '');
  const user = users.find((candidate) => {
    const candidateId = normalizeTelegramPeerId(candidate?.id || '');
    return fullUserId && candidateId && candidateId === fullUserId;
  }) || users[0] || fallbackEntity || null;
  const about = cleanTelegramText(
    fullUser?.about
    || fullUser?.bio
    || user?.about
    || user?.bio
    || '',
    2400
  );
  const birthday = normalizeTelegramBirthdayValue(fullUser?.birthday || user?.birthday || null);
  return {
    username: cleanTelegramText(user?.username || user?.userName || fallbackEntity?.username || '', 120),
    phone: cleanTelegramText(user?.phone || fallbackEntity?.phone || '', 80),
    about,
    bio: about,
    birthday
  };
}

function applyTelegramProfileDetails(target = null, details = null) {
  if (!target || typeof target !== 'object' || !details || typeof details !== 'object') return target;
  const patch = {
    username: cleanTelegramText(details.username || '', 120),
    phone: cleanTelegramText(details.phone || '', 80),
    about: cleanTelegramText(details.about || details.bio || '', 2400),
    bio: cleanTelegramText(details.bio || details.about || '', 2400),
    birthday: cleanTelegramText(details.birthday || '', 120)
  };
  if (patch.username) target.username = patch.username;
  if (patch.phone) target.phone = patch.phone;
  if (patch.about) target.about = patch.about;
  if (patch.bio) target.bio = patch.bio;
  if (patch.birthday) target.birthday = patch.birthday;

  target.details = {
    ...(target.details && typeof target.details === 'object' ? target.details : {}),
    ...Object.fromEntries(Object.entries(patch).filter(([, value]) => Boolean(value)))
  };
  if (target.profile && typeof target.profile === 'object') {
    target.profile = {
      ...target.profile,
      ...(patch.username ? { username: patch.username } : {}),
      ...(patch.phone ? { phone: patch.phone } : {}),
      ...(patch.about ? { about: patch.about } : {}),
      ...(patch.bio ? { bio: patch.bio } : {}),
      ...(patch.birthday ? { birthday: patch.birthday } : {}),
      details: {
        ...(target.profile.details && typeof target.profile.details === 'object' ? target.profile.details : {}),
        ...Object.fromEntries(Object.entries(patch).filter(([, value]) => Boolean(value)))
      }
    };
  }
  return target;
}

function isTelegramUserEntity(entity = null) {
  if (!entity || typeof entity !== 'object') return false;
  const className = cleanTelegramText(entity.className || entity.constructor?.name || '', 120);
  return Boolean(
    /User/iu.test(className)
    || entity.firstName
    || entity.lastName
    || entity.username
    || entity.phone
  ) && !entity.title;
}

async function fetchTelegramFullUserDetails(client = null, entity = null) {
  if (!client || !entity || typeof entity !== 'object' || !isTelegramUserEntity(entity)) return null;
  const dependency = getTelegramDependency();
  if (!dependency.ok || !dependency.Api?.users?.GetFullUser) return null;
  let inputEntity = entity;
  if (typeof client.getInputEntity === 'function') {
    inputEntity = await client.getInputEntity(entity).catch(() => entity);
  }
  const result = await withTelegramTimeout(
    client.invoke(new dependency.Api.users.GetFullUser({ id: inputEntity })),
    TELEGRAM_PROFILE_TIMEOUT_MS,
    'Загрузка профиля Telegram'
  );
  return extractTelegramFullUserDetails(result, entity);
}

async function hydrateTelegramParticipantDetails(pairs = [], client = null, options = {}) {
  const sourcePairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => pair?.normalized && pair?.user && isTelegramUserEntity(pair.user))
    .slice(0, Math.max(1, Math.min(80, Number(options.limit || 32) || 32)));
  if (!sourcePairs.length || !client) return;
  const deadline = Date.now() + Math.max(1500, Math.min(TELEGRAM_PROFILE_TIMEOUT_MS * 2, Number(options.budgetMs || 9000) || 9000));
  let cursor = 0;
  const workers = Array.from({ length: Math.min(4, sourcePairs.length) }, async () => {
    while (Date.now() < deadline) {
      const index = cursor;
      cursor += 1;
      if (index >= sourcePairs.length) return;
      const pair = sourcePairs[index];
      const details = await fetchTelegramFullUserDetails(client, pair.user).catch(() => null);
      if (details) {
        applyTelegramProfileDetails(pair.normalized, details);
      }
    }
  });
  await Promise.allSettled(workers);
}

async function hydrateTelegramDialogProfileDetails(pairs = [], client = null) {
  const participantPairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => pair?.normalized?.type === 'direct')
    .map((pair) => ({
      user: pair?.dialog?.entity || pair?.dialog?.inputEntity || null,
      normalized: pair?.normalized || null
    }))
    .filter((pair) => pair.user && pair.normalized);
  await hydrateTelegramParticipantDetails(participantPairs, client, {
    limit: 36,
    budgetMs: 9000
  });
}

function normalizeTelegramParticipant(user = null, settings = null) {
  if (!user || typeof user !== 'object') return null;
  const peerId = normalizeTelegramPeerId(
    user.id
    || user.userId
    || user.peerId
    || user.inputPeer?.userId
    || user.inputPeer?.channelId
    || user.inputPeer?.chatId
    || ''
  );
  if (!peerId) return null;
  const username = cleanTelegramText(user.username || user.userName || '', 120);
  const label = getTelegramEntityDisplayName(
    user,
    username ? `@${username}` : `Telegram ${peerId}`
  ) || (username ? `@${username}` : `Telegram ${peerId}`);
  const avatarCacheKey = buildTelegramAvatarCacheKey(user, peerId);
  const avatarResourceUrl = rememberTelegramAvatarRecord(user, peerId, settings, null);
  const cachedAvatarUrl = getCachedTelegramAvatarDataUrl(avatarCacheKey);
  const status = normalizeTelegramStatus(user);
  const memberId = `telegram:${peerId}`;
  const phone = cleanTelegramText(user.phone || '', 80);
  const about = cleanTelegramText(user.about || user.bio || '', 2400);
  const birthday = normalizeTelegramBirthdayValue(user.birthday || null);
  const avatarUrl = cachedAvatarUrl || avatarResourceUrl;
  const details = {
    username,
    phone,
    about,
    bio: about,
    birthday
  };
  return {
    id: memberId,
    memberId,
    peerId,
    label,
    title: label,
    username,
    phone,
    about,
    bio: about,
    birthday,
    details,
    profile: {
      id: memberId,
      memberId,
      peerId,
      fullName: label,
      displayName: label,
      name: label,
      label,
      title: label,
      username,
      phone,
      about,
      bio: about,
      birthday,
      avatarUrl,
      photoUrl: avatarUrl,
      details
    },
    statusText: cleanTelegramText(status.text || '', 120),
    statusKind: cleanTelegramText(status.kind || '', 120),
    presence: status.presence,
    avatarUrl,
    avatarCacheKey,
    avatarResourceUrl,
    isBot: user.bot === true
  };
}

async function resolveTelegramSelfParticipant(client = null, settings = null) {
  if (!client || typeof client.getMe !== 'function') return null;
  const user = await withTelegramTimeout(
    client.getMe(),
    TELEGRAM_MESSAGES_TIMEOUT_MS,
    'Загрузка профиля Telegram'
  ).catch(() => null);
  const normalized = normalizeTelegramParticipant(user, settings);
  if (!normalized) return null;
  const pair = {
    user,
    normalized: {
      ...normalized,
      id: 'telegram:self',
      memberId: 'telegram:self',
      actualMemberId: normalized.memberId
    }
  };
  await hydrateTelegramParticipantAvatarDataUrls([pair], client).catch(() => null);
  await hydrateTelegramParticipantDetails([pair], client, { limit: 1 }).catch(() => null);
  rememberTelegramEntity('telegram:self', user);
  return pair.normalized;
}

async function hydrateTelegramParticipantAvatarDataUrls(pairs = [], client = null) {
  const sourcePairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => pair?.normalized && hasTelegramProfilePhoto(pair?.user))
    .slice(0, TELEGRAM_DIALOG_AVATAR_LIMIT);
  if (!sourcePairs.length || !client) return;
  const deadline = Date.now() + Math.min(TELEGRAM_DIALOG_AVATAR_BUDGET_MS, 4500);
  let cursor = 0;
  const workers = Array.from({
    length: Math.min(TELEGRAM_DIALOG_AVATAR_CONCURRENCY, sourcePairs.length)
  }, async () => {
    while (Date.now() < deadline) {
      const index = cursor;
      cursor += 1;
      if (index >= sourcePairs.length) return;
      const pair = sourcePairs[index];
      const body = await downloadTelegramProfilePhoto(client, {
        entity: pair.user || null,
        inputEntity: pair.user || null,
        avatarCacheKey: pair.normalized?.avatarCacheKey || '',
        peerId: pair.normalized?.peerId || ''
      }, TELEGRAM_AVATAR_DOWNLOAD_TIMEOUT_MS).catch(() => Buffer.alloc(0));
      if (body.length > 0) {
        pair.normalized.avatarUrl = buildTelegramAvatarDataUrl(body, 'image/jpeg');
      }
    }
  });
  await Promise.allSettled(workers);
}

function getTelegramForwardedSource(message = null) {
  const header = message?.fwdFrom || message?.forward || null;
  if (!header || typeof header !== 'object') return null;
  const sourceType = header.fromId?.userId || header.savedFromPeer?.userId
    ? 'PRIVATE'
    : (header.fromId?.channelId || header.savedFromPeer?.channelId ? 'CHANNEL' : (header.fromId?.chatId || header.savedFromPeer?.chatId ? 'GROUP' : ''));
  const fromName = cleanTelegramText(
    header.fromName
    || header.postAuthor
    || header.title
    || header.chatTitle
    || getTelegramEntityDisplayName(header.chat, '')
    || getTelegramEntityDisplayName(header.channel, '')
    || getTelegramEntityDisplayName(header.from, '')
    || getTelegramEntityDisplayName(header.savedFromPeer, '')
    || '',
    160
  );
  const fromId = normalizeTelegramPeerId(
    header.fromId?.userId
    || header.fromId?.channelId
    || header.fromId?.chatId
    || header.savedFromPeer?.userId
    || header.savedFromPeer?.channelId
    || header.savedFromPeer?.chatId
    || ''
  );
  if (!fromName && !fromId) return null;
  return {
    title: fromName || `Telegram ${fromId}`,
    authorName: fromName || '',
    memberId: fromId ? `telegram:${fromId}` : '',
    workspaceId: 'telegram',
    chatId: fromId ? normalizeTelegramChatId(fromId) : '',
    sourceLabel: 'Telegram',
    sourceType,
    messageId: cleanTelegramText(
      header.savedFromMsgId
      || header.channelPost
      || header.savedFromMsgID
      || '',
      120
    )
  };
}

function getTelegramReplyToMessageId(message = null) {
  return cleanTelegramText(
    message?.replyTo?.replyToMsgId
    || message?.replyTo?.replyToTopId
    || message?.replyToMsgId
    || '',
    80
  );
}

function getTelegramDocumentAttribute(document = null, pattern = null) {
  const attrs = Array.isArray(document?.attributes) ? document.attributes : [];
  return attrs.find((attr) => {
    const className = cleanTelegramText(attr?.className || attr?.constructor?.name || '', 120);
    return pattern instanceof RegExp ? pattern.test(className) : false;
  }) || null;
}

function getTelegramDocumentFileName(document = null, fallback = 'telegram-file') {
  const fileNameAttr = getTelegramDocumentAttribute(document, /DocumentAttributeFilename/iu);
  return sanitizeOpenFileName(
    fileNameAttr?.fileName
    || document?.fileName
    || document?.name
    || fallback,
    fallback
  );
}

function getTelegramPhotoDimensions(photo = null) {
  const sizes = Array.isArray(photo?.sizes) ? photo.sizes : [];
  const candidates = sizes
    .map((size) => ({
      width: Math.max(0, Math.trunc(Number(size?.w || size?.width || 0) || 0)),
      height: Math.max(0, Math.trunc(Number(size?.h || size?.height || 0) || 0)),
      size: Math.max(0, Math.trunc(Number(size?.size || 0) || 0))
    }))
    .sort((left, right) => ((right.width * right.height) || right.size) - ((left.width * left.height) || left.size));
  return candidates[0] || { width: 0, height: 0, size: 0 };
}

function getTelegramDocumentDimensions(document = null) {
  const videoAttr = getTelegramDocumentAttribute(document, /DocumentAttributeVideo/iu);
  const imageAttr = getTelegramDocumentAttribute(document, /DocumentAttributeImageSize/iu);
  const attr = videoAttr || imageAttr || null;
  return {
    width: Math.max(0, Math.trunc(Number(attr?.w || attr?.width || 0) || 0)),
    height: Math.max(0, Math.trunc(Number(attr?.h || attr?.height || 0) || 0)),
    durationSeconds: Math.max(0, Math.trunc(Number(videoAttr?.duration || 0) || 0)),
    isVideoNote: videoAttr?.roundMessage === true
  };
}

function getTelegramAudioMeta(document = null) {
  const audioAttr = getTelegramDocumentAttribute(document, /DocumentAttributeAudio/iu);
  if (!audioAttr) {
    return {
      durationSeconds: 0,
      isVoice: false,
      title: '',
      performer: ''
    };
  }
  return {
    durationSeconds: Math.max(0, Math.trunc(Number(audioAttr.duration || 0) || 0)),
    isVoice: audioAttr.voice === true,
    title: cleanTelegramText(audioAttr.title || '', 140),
    performer: cleanTelegramText(audioAttr.performer || '', 140)
  };
}

function pruneTelegramMediaCache(maxEntries = 640) {
  while (telegramMediaTokenToRecord.size > maxEntries) {
    const oldestKey = telegramMediaTokenToRecord.keys().next().value;
    if (!oldestKey) break;
    telegramMediaTokenToRecord.delete(oldestKey);
  }
}

function buildTelegramMediaUrl(token = '', fileName = 'telegram-file.bin') {
  const safeToken = cleanTelegramText(token || '', 180);
  if (!safeToken) return '';
  const safeName = sanitizeOpenFileName(fileName, 'telegram-file.bin');
  return `${LOCAL_ASSET_PROTOCOL}://telegram/${encodeURIComponent(safeToken)}/${encodeURIComponent(safeName)}`;
}

function rememberTelegramMediaRecord(record = null) {
  if (!record || typeof record !== 'object' || !record.token) return '';
  telegramMediaTokenToRecord.set(record.token, {
    ...record,
    createdAt: Date.now()
  });
  pruneTelegramMediaCache();
  return buildTelegramMediaUrl(record.token, record.fileName || 'telegram-file.bin');
}

function buildTelegramAvatarCacheKey(entity = null, peerId = '') {
  const photo = entity && typeof entity === 'object' ? entity.photo : null;
  if (!photo || typeof photo !== 'object') return '';
  const photoId = normalizeTelegramPeerId(photo.photoId || photo.id || '');
  const peer = normalizeTelegramPeerId(peerId || entity?.id || entity?.userId || entity?.channelId || entity?.chatId || '');
  return cleanTelegramText(
    [peer || 'peer', photoId || 'photo'].join('-').replace(/[^a-z0-9_-]+/giu, '-'),
    180
  );
}

function getTelegramAvatarCachePath(cacheKey = '') {
  const safeKey = cleanTelegramText(cacheKey || '', 180).replace(/[^a-z0-9_-]+/giu, '-');
  if (!safeKey) return '';
  const dirPath = path.join(app.getPath('userData'), YUCHAT_STORAGE_PROFILE_NAME, 'telegram-avatars');
  ensureDirSync(dirPath);
  return path.join(dirPath, `${safeKey}.jpg`);
}

function readTelegramAvatarCache(cacheKey = '') {
  const safeKey = cleanTelegramText(cacheKey || '', 180);
  if (!safeKey) return Buffer.alloc(0);
  const cachedDataUrl = telegramAvatarDataUrlCache.get(safeKey) || '';
  if (cachedDataUrl) {
    const base64 = String(cachedDataUrl || '').replace(/^data:image\/[a-z0-9.+-]+;base64,/i, '');
    return Buffer.from(base64, 'base64');
  }
  const filePath = getTelegramAvatarCachePath(safeKey);
  if (!filePath || !fs.existsSync(filePath)) return Buffer.alloc(0);
  try {
    const body = fs.readFileSync(filePath);
    if (body.length > 0) {
      telegramAvatarDataUrlCache.set(safeKey, buildTelegramAvatarDataUrl(body, 'image/jpeg'));
    }
    return body;
  } catch {
    return Buffer.alloc(0);
  }
}

function getCachedTelegramAvatarDataUrl(cacheKey = '') {
  const safeKey = cleanTelegramText(cacheKey || '', 180);
  if (!safeKey) return '';
  const cached = telegramAvatarDataUrlCache.get(safeKey) || '';
  if (cached) return cached;
  const body = readTelegramAvatarCache(safeKey);
  return body.length > 0 ? buildTelegramAvatarDataUrl(body, 'image/jpeg') : '';
}

function writeTelegramAvatarCache(cacheKey = '', body = null) {
  const safeKey = cleanTelegramText(cacheKey || '', 180);
  const buffer = Buffer.isBuffer(body) ? body : Buffer.alloc(0);
  if (!safeKey || !buffer.length) return false;
  telegramAvatarDataUrlCache.set(safeKey, buildTelegramAvatarDataUrl(buffer, 'image/jpeg'));
  try {
    const filePath = getTelegramAvatarCachePath(safeKey);
    if (!filePath) return false;
    fs.writeFileSync(filePath, buffer);
    return true;
  } catch {
    return false;
  }
}

function hasTelegramProfilePhoto(entity = null) {
  const photo = entity && typeof entity === 'object' ? entity.photo : null;
  if (!photo || typeof photo !== 'object') return false;
  const className = cleanTelegramText(photo.className || photo.constructor?.name || '', 120);
  return !/Empty/iu.test(className);
}

function rememberTelegramAvatarRecord(entity = null, peerId = '', settings = null, inputEntity = null) {
  if (!hasTelegramProfilePhoto(entity)) return '';
  const photoId = normalizeTelegramPeerId(entity?.photo?.photoId || entity?.photo?.id || '');
  const avatarCacheKey = buildTelegramAvatarCacheKey(entity, peerId);
  const tokenBase = cleanTelegramText(
    String([peerId || entity?.id || `avatar-${Date.now()}`, photoId].filter(Boolean).join('-'))
      .replace(/[^a-z0-9_-]+/giu, '-'),
    120
  ) || `avatar-${Date.now()}`;
  return rememberTelegramMediaRecord({
    token: `${tokenBase}-avatar`,
    kind: 'profile-photo',
    entity,
    inputEntity,
    peerId: normalizeTelegramPeerId(peerId || entity?.id || ''),
    avatarCacheKey,
    settings: normalizeTelegramApiSettings(settings),
    fileName: `telegram-avatar-${tokenBase}.jpg`,
    mimeType: 'image/jpeg'
  });
}

function bufferFromTelegramDownloadResult(result = null) {
  if (Buffer.isBuffer(result)) return result;
  if (typeof result === 'string' && fs.existsSync(result)) return fs.readFileSync(result);
  return Buffer.alloc(0);
}

async function downloadTelegramProfilePhoto(client = null, record = null, timeoutMs = TELEGRAM_AVATAR_DOWNLOAD_TIMEOUT_MS) {
  if (!client || !record || typeof record !== 'object') return Buffer.alloc(0);
  const cacheKey = cleanTelegramText(
    record.avatarCacheKey
    || buildTelegramAvatarCacheKey(record.entity || null, record.peerId || getTelegramPeerIdFromChatId(record.chatId || '')),
    180
  );
  if (cacheKey) {
    const cachedBody = readTelegramAvatarCache(cacheKey);
    if (cachedBody.length > 0) return cachedBody;
  }
  const candidates = [
    record.entity,
    record.inputEntity,
    record.peerId ? String(record.peerId) : '',
    record.chatId ? getTelegramPeerIdFromChatId(record.chatId) : ''
  ].filter(Boolean);
  const seen = new Set();
  for (const candidate of candidates) {
    const key = typeof candidate === 'object'
      ? `${candidate.className || candidate.constructor?.name || 'object'}:${normalizeTelegramPeerId(candidate.id || candidate.userId || candidate.channelId || candidate.chatId || '')}`
      : String(candidate || '');
    if (seen.has(key)) continue;
    seen.add(key);
    try {
      const result = await withTelegramTimeout(
        client.downloadProfilePhoto(candidate, { isBig: false }),
        timeoutMs,
        'Загрузка Telegram-аватара'
      );
      const body = bufferFromTelegramDownloadResult(result);
      if (body.length > 0) {
        if (cacheKey) {
          writeTelegramAvatarCache(cacheKey, body);
        }
        return body;
      }
    } catch {
      // Try the next entity shape; Telegram dialogs can expose users/channels differently.
    }
  }
  return Buffer.alloc(0);
}

function buildTelegramAvatarDataUrl(body = null, mimeType = 'image/jpeg') {
  const buffer = Buffer.isBuffer(body) ? body : Buffer.alloc(0);
  if (!buffer.length) return '';
  const safeMimeType = cleanTelegramText(mimeType || 'image/jpeg', 80) || 'image/jpeg';
  return `data:${safeMimeType};base64,${buffer.toString('base64')}`;
}

async function hydrateTelegramDialogAvatarDataUrls(pairs = [], client = null) {
  const sourcePairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => pair?.normalized && hasTelegramProfilePhoto(pair?.dialog?.entity))
    .slice(0, TELEGRAM_DIALOG_AVATAR_LIMIT);
  if (!sourcePairs.length || !client) return;
  const deadline = Date.now() + TELEGRAM_DIALOG_AVATAR_BUDGET_MS;
  let cursor = 0;
  const workers = Array.from({
    length: Math.min(TELEGRAM_DIALOG_AVATAR_CONCURRENCY, sourcePairs.length)
  }, async () => {
    while (Date.now() < deadline) {
      const index = cursor;
      cursor += 1;
      if (index >= sourcePairs.length) return;
      const pair = sourcePairs[index];
      const normalized = pair.normalized;
      const body = await downloadTelegramProfilePhoto(client, {
        entity: pair.dialog?.entity || null,
        inputEntity: pair.dialog?.inputEntity || null,
        avatarCacheKey: normalized.avatarCacheKey || '',
        peerId: normalized.id || '',
        chatId: normalized.chatId || ''
      }).catch(() => Buffer.alloc(0));
      const dataUrl = buildTelegramAvatarDataUrl(body);
      if (dataUrl) {
        normalized.avatarUrl = dataUrl;
      }
    }
  });
  await Promise.allSettled(workers);
}

async function hydrateTelegramDialogPreviewAuthorData(pairs = [], client = null, settings = null) {
  const sourcePairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => {
      const normalized = pair?.normalized || null;
      const message = pair?.dialog?.message || null;
      if (!normalized || !message || typeof message !== 'object') return false;
      if (normalized.type === 'direct') return false;
      if (message.out === true || message.isMine === true || message.outgoing === true) return false;
      return Boolean(getTelegramSenderId(message) || getTelegramMessageSenderEntity(message) || message.postAuthor);
    })
    .slice(0, TELEGRAM_DIALOG_AVATAR_LIMIT);
  if (!sourcePairs.length) return;

  const deadline = Date.now() + Math.min(TELEGRAM_DIALOG_AVATAR_BUDGET_MS, 5200);
  let cursor = 0;
  const workers = Array.from({
    length: Math.min(TELEGRAM_DIALOG_AVATAR_CONCURRENCY, sourcePairs.length)
  }, async () => {
    while (Date.now() < deadline) {
      const index = cursor;
      cursor += 1;
      if (index >= sourcePairs.length) return;

      const pair = sourcePairs[index];
      const normalized = pair.normalized;
      const message = pair.dialog?.message || null;
      const senderId = getTelegramSenderId(message);
      let senderEntity = getTelegramMessageSenderEntity(message);

      if (!senderEntity && senderId && client) {
        senderEntity = await withTelegramTimeout(
          resolveTelegramSenderEntity(client, message),
          TELEGRAM_AVATAR_DOWNLOAD_TIMEOUT_MS,
          'Загрузка автора Telegram-превью'
        ).catch(() => null);
      }

      const author = getTelegramMessageAuthor(message, senderEntity);
      if (isMeaningfulTelegramPreviewAuthorName(author.name, senderId)) {
        normalized.previewAuthor = cleanTelegramText(author.name || '', 160);
        normalized.previewAuthorMemberId = cleanTelegramText(author.memberId || '', 160);
      }

      if (!senderEntity || !normalized.previewAuthor || !client || !hasTelegramProfilePhoto(senderEntity)) {
        continue;
      }

      const peerId = normalizeTelegramPeerId(senderId || senderEntity.id || '');
      const avatarCacheKey = buildTelegramAvatarCacheKey(senderEntity, peerId);
      normalized.previewAuthorAvatarResourceUrl = rememberTelegramAvatarRecord(senderEntity, peerId, settings, senderEntity);
      const body = await downloadTelegramProfilePhoto(client, {
        entity: senderEntity,
        inputEntity: senderEntity,
        avatarCacheKey,
        peerId
      }).catch(() => Buffer.alloc(0));
      const dataUrl = buildTelegramAvatarDataUrl(body);
      if (dataUrl) {
        normalized.previewAuthorAvatarUrl = dataUrl;
      }
    }
  });
  await Promise.allSettled(workers);
}

function normalizeTelegramMessageAttachments(message = null, chatId = '', settings = null) {
  if (!message || typeof message !== 'object' || !message.media) return [];
  const media = message.media;
  const messageId = getTelegramMessageId(message);
  const tokenBase = cleanTelegramText(`${chatId}-${messageId}`.replace(/[^a-z0-9_-]+/giu, '-'), 120) || `tg-${Date.now()}`;
  const className = cleanTelegramText(media?.className || media?.constructor?.name || '', 120);
  const attachments = [];
  const pushMediaAttachment = (attachment = null) => {
    if (!attachment || typeof attachment !== 'object') return;
    const index = attachments.length;
    const fileName = sanitizeOpenFileName(attachment.name || `telegram-${messageId || Date.now()}-${index + 1}`, 'telegram-file.bin');
    const token = `${tokenBase}-${index + 1}`;
    const url = rememberTelegramMediaRecord({
      token,
      chatId,
      messageId,
      media,
      message,
      settings: normalizeTelegramApiSettings(settings),
      fileName,
      mimeType: attachment.mimeType || 'application/octet-stream'
    });
    attachments.push({
      id: `telegram:${token}`,
      fileId: `telegram:${token}`,
      name: fileName,
      url,
      downloadUrl: url,
      previewUrl: attachment.previewUrl || '',
      size: Math.max(0, Math.trunc(Number(attachment.size || 0) || 0)),
      mimeType: cleanTelegramText(attachment.mimeType || '', 140),
      mediaType: cleanTelegramText(attachment.mediaType || '', 80),
      isVideoNote: attachment.isVideoNote === true,
      isVoice: attachment.isVoice === true,
      voice: attachment.isVoice === true,
      voiceNote: attachment.isVoice === true,
      durationSeconds: Math.max(0, Math.trunc(Number(attachment.durationSeconds || 0) || 0)),
      width: Math.max(0, Math.trunc(Number(attachment.width || 0) || 0)),
      height: Math.max(0, Math.trunc(Number(attachment.height || 0) || 0))
    });
  };

  if (media.photo || /MessageMediaPhoto/iu.test(className)) {
    const photo = media.photo || media;
    const dimensions = getTelegramPhotoDimensions(photo);
    pushMediaAttachment({
      name: `photo-${messageId || Date.now()}.jpg`,
      mimeType: 'image/jpeg',
      mediaType: 'PHOTO',
      size: dimensions.size,
      width: dimensions.width,
      height: dimensions.height
    });
    return attachments;
  }

  if (media.document || /MessageMediaDocument/iu.test(className)) {
    const document = media.document || media;
    const mimeType = cleanTelegramText(document?.mimeType || 'application/octet-stream', 140) || 'application/octet-stream';
    const dimensions = getTelegramDocumentDimensions(document);
    const audioMeta = getTelegramAudioMeta(document);
    const fallbackBase = /^image\//iu.test(mimeType)
      ? `image-${messageId || Date.now()}${getFileExtensionByContentType(mimeType) || '.jpg'}`
      : /^video\//iu.test(mimeType)
        ? `video-${messageId || Date.now()}${getFileExtensionByContentType(mimeType) || '.mp4'}`
        : /^audio\//iu.test(mimeType)
          ? `audio-${messageId || Date.now()}${getFileExtensionByContentType(mimeType) || '.ogg'}`
          : `file-${messageId || Date.now()}${getFileExtensionByContentType(mimeType) || '.bin'}`;
    pushMediaAttachment({
      name: getTelegramDocumentFileName(document, fallbackBase),
      mimeType,
      mediaType: dimensions.isVideoNote ? 'VIDEO_NOTE' : '',
      size: document?.size || 0,
      width: dimensions.width,
      height: dimensions.height,
      durationSeconds: Math.max(dimensions.durationSeconds, audioMeta.durationSeconds),
      isVideoNote: dimensions.isVideoNote,
      isVoice: audioMeta.isVoice
    });
    return attachments;
  }

  return attachments;
}

function getTelegramMessageEntitySourceText(message = null, fallbackText = '') {
  if (!message || typeof message !== 'object') {
    return String(fallbackText ?? '').replace(/\r\n?/g, '\n');
  }
  const candidates = [
    message.message,
    message.text,
    message.caption,
    message.message?.message,
    message.message?.text,
    message.message?.caption,
    fallbackText
  ];
  for (const candidate of candidates) {
    if (typeof candidate !== 'string' && typeof candidate !== 'number') continue;
    const source = String(candidate ?? '').replace(/\r\n?/g, '\n');
    if (source) return source;
  }
  return String(fallbackText ?? '').replace(/\r\n?/g, '\n');
}

function extractTelegramMessageEntityLinks(message = null, text = '') {
  if (!message || typeof message !== 'object') return [];
  const sourceText = getTelegramMessageEntitySourceText(message, text);
  const entities = [
    ...(Array.isArray(message.entities) ? message.entities : []),
    ...(Array.isArray(message.message?.entities) ? message.message.entities : [])
  ];
  const links = [];
  const seen = new Set();
  entities.forEach((entity) => {
    if (!entity || typeof entity !== 'object') return;
    const className = cleanTelegramText(entity.className || entity.constructor?.name || '', 120);
    let url = cleanTelegramText(entity.url || '', 4096);
    if (!url && /MessageEntityUrl/iu.test(className)) {
      const offset = Math.max(0, Number(entity.offset || 0) || 0);
      const length = Math.max(0, Number(entity.length || 0) || 0);
      url = cleanTelegramText(sourceText.slice(offset, offset + length), 4096);
    }
    if (!/^https?:\/\//iu.test(url)) return;
    if (seen.has(url)) return;
    seen.add(url);
    links.push(url);
  });
  return links;
}

function formatTelegramMessageTextWithEntities(message = null, fallbackText = '') {
  if (!message || typeof message !== 'object') return cleanTelegramMultiline(fallbackText || '', 6000);
  const sourceText = getTelegramMessageEntitySourceText(message, fallbackText);
  if (!cleanTelegramMultiline(sourceText, 6000)) return '';
  const entities = [
    ...(Array.isArray(message.entities) ? message.entities : []),
    ...(Array.isArray(message.message?.entities) ? message.message.entities : [])
  ]
    .map((entity) => {
      if (!entity || typeof entity !== 'object') return null;
      const offset = Math.max(0, Math.trunc(Number(entity.offset || 0) || 0));
      const length = Math.max(0, Math.trunc(Number(entity.length || 0) || 0));
      if (length <= 0 || offset >= sourceText.length) return null;
      const end = Math.min(sourceText.length, offset + length);
      if (end <= offset) return null;
      const className = cleanTelegramText(entity.className || entity.constructor?.name || '', 120);
      const url = cleanTelegramText(entity.url || '', 4096);
      return { offset, end, className, url };
    })
    .filter(Boolean)
    .sort((left, right) => right.offset - left.offset || right.end - left.end);
  if (!entities.length) return sourceText;

  let formatted = sourceText;
  entities.forEach((entity) => {
    const before = formatted.slice(0, entity.offset);
    const inner = formatted.slice(entity.offset, entity.end);
    const after = formatted.slice(entity.end);
    let replacement = inner;
    if (/MessageEntityBold/iu.test(entity.className)) {
      replacement = `**${inner}**`;
    } else if (/MessageEntityItalic/iu.test(entity.className)) {
      replacement = `_${inner}_`;
    } else if (/MessageEntityUnderline/iu.test(entity.className)) {
      replacement = `__${inner}__`;
    } else if (/MessageEntityStrike/iu.test(entity.className)) {
      replacement = `~~${inner}~~`;
    } else if (/MessageEntityCode/iu.test(entity.className)) {
      replacement = `\`${inner.replace(/`/g, '\\`')}\``;
    } else if (/MessageEntityPre/iu.test(entity.className)) {
      replacement = `\n\`\`\`\n${inner.replace(/```/g, '\\`\\`\\`')}\n\`\`\`\n`;
    } else if (/MessageEntityTextUrl/iu.test(entity.className) && /^https?:\/\//iu.test(entity.url)) {
      replacement = `[${inner}](${entity.url})`;
    }
    formatted = `${before}${replacement}${after}`;
  });
  return cleanTelegramMultiline(formatted, 6000);
}

function getTelegramPollMedia(message = null) {
  const mediaPoll = message?.media?.poll || message?.poll || null;
  if (!mediaPoll || typeof mediaPoll !== 'object') return null;
  const poll = mediaPoll.poll || mediaPoll;
  if (!poll || typeof poll !== 'object') return null;
  return {
    poll,
    results: mediaPoll.results || message?.media?.results || message?.poll?.results || null
  };
}

function readTelegramNumericValue(value = null, depth = 0) {
  if (value == null || depth > 3) return 0;
  if (typeof value === 'number') {
    return Number.isFinite(value) ? value : 0;
  }
  if (typeof value === 'bigint') {
    try {
      return Number(value);
    } catch {
      return 0;
    }
  }
  if (typeof value === 'string') {
    const parsed = Number(value);
    return Number.isFinite(parsed) ? parsed : 0;
  }
  if (typeof value === 'object') {
    const nestedCandidates = [
      value.value,
      value.low,
      value.high,
      value.voters,
      value.count,
      value.total,
      value.totalVoters
    ];
    for (const candidate of nestedCandidates) {
      const numeric = readTelegramNumericValue(candidate, depth + 1);
      if (numeric !== 0) {
        return numeric;
      }
    }
    if (typeof value.toString === 'function') {
      const stringified = String(value.toString());
      if (stringified && stringified !== '[object Object]') {
        const parsed = Number(stringified);
        if (Number.isFinite(parsed)) return parsed;
      }
    }
  }
  return 0;
}

function isTelegramTruthyFlag(value = null) {
  if (value === true || value === 1) return true;
  if (typeof value === 'string') {
    return /^(?:1|true|yes|y)$/iu.test(value.trim());
  }
  return false;
}

function telegramPollOptionBufferToBase64(value = null) {
  if (Buffer.isBuffer(value)) return value.toString('base64url');
  if (value instanceof Uint8Array) return Buffer.from(value).toString('base64url');
  if (value instanceof ArrayBuffer) return Buffer.from(new Uint8Array(value)).toString('base64url');
  if (ArrayBuffer.isView(value)) {
    return Buffer.from(value.buffer, value.byteOffset, value.byteLength).toString('base64url');
  }
  if (Array.isArray(value)) return Buffer.from(value).toString('base64url');
  if (typeof value === 'string') return Buffer.from(value).toString('base64url');
  if (value && typeof value === 'object') {
    const nested = [
      value.option,
      value.bytes,
      value.byteArray,
      value.data,
      value.buffer,
      value.value
    ];
    for (const candidate of nested) {
      const encoded = telegramPollOptionBufferToBase64(candidate);
      if (encoded) return encoded;
    }
  }
  return '';
}

function telegramPollOptionId(value = null, index = 0, text = '') {
  const encoded = telegramPollOptionBufferToBase64(value);
  return cleanTelegramText(
    `tg-${encoded || `${index + 1}-${text}`}`.toLowerCase().replace(/[^a-z0-9._-]+/giu, '-'),
    120
  ) || `tg-${index + 1}`;
}

function telegramPollOptionIdFromResult(value = null, index = 0) {
  if (value == null) return '';
  if (
    Buffer.isBuffer(value)
    || value instanceof Uint8Array
    || value instanceof ArrayBuffer
    || ArrayBuffer.isView(value)
    || Array.isArray(value)
  ) {
    return telegramPollOptionId(value, index, '');
  }
  if (typeof value === 'string') {
    const normalized = cleanTelegramText(value || '', 120).toLowerCase();
    if (/^tg-[a-z0-9._-]+$/iu.test(normalized)) return normalized;
  }
  const source = value && typeof value === 'object'
    ? (
      value.option
      || value.answer
      || value.optionBytes
      || value.bytes
      || value.byteArray
      || value.data
      || value.buffer
      || value.value
      || value
    )
    : value;
  return telegramPollOptionId(source, index, '');
}

function getTelegramNativePollPayload(message = null, chatId = '') {
  const media = getTelegramPollMedia(message);
  const poll = media?.poll || null;
  if (!poll || typeof poll !== 'object') return null;
  const question = cleanTelegramMultiline(getTelegramTextWithEntitiesText(poll.question || poll.title || ''), 600);
  if (!question) return null;
  const answers = (Array.isArray(poll.answers) ? poll.answers : [])
    .map((answer, index) => {
      const text = cleanTelegramMultiline(getTelegramTextWithEntitiesText(answer?.text || answer?.title || `Вариант ${index + 1}`), 220);
      const optionBase64 = telegramPollOptionBufferToBase64(answer?.option || null);
      const id = telegramPollOptionId(answer?.option || null, index, text);
      return text ? {
        id,
        text,
        telegramOption: optionBase64,
        voteCount: 0,
        percent: 0
      } : null;
    })
    .filter(Boolean)
    .slice(0, 10);
  if (answers.length < 2) return null;

  const results = media?.results && typeof media.results === 'object' ? media.results : null;
  const totalVotersHint = Math.max(0, Math.trunc(readTelegramNumericValue(results?.totalVoters) || 0));
  const chosenOptionIds = new Set();
  const resultById = new Map();
  const knownAnswerIds = new Set(answers.map((answer) => answer.id).filter(Boolean));
  const resolveKnownPollOptionId = (value = null, index = 0) => {
    const candidates = [telegramPollOptionIdFromResult(value, index)];
    if (typeof value === 'string') {
      const normalized = cleanTelegramText(value || '', 120).toLowerCase();
      if (normalized && !/^tg-/iu.test(normalized)) {
        candidates.push(cleanTelegramText(`tg-${normalized}`.replace(/[^a-z0-9._-]+/giu, '-'), 120));
      }
    } else if (value && typeof value === 'object') {
      const explicitId = cleanTelegramText(value.id || value.optionId || '', 120).toLowerCase();
      if (/^tg-[a-z0-9._-]+$/iu.test(explicitId)) {
        candidates.push(explicitId);
      }
    }
    return candidates.find((id) => id && knownAnswerIds.has(id))
      || candidates.find(Boolean)
      || '';
  };
  (Array.isArray(results?.results) ? results.results : []).forEach((result) => {
    const resultOptionValue = result?.option || result?.answer || result?.optionBytes || null;
    const id = resolveKnownPollOptionId(
      resultOptionValue,
      Number(result?.index ?? result?.optionIndex ?? 0) || 0
    );
    if (!id) return;
    const voters = Math.max(0, Math.trunc(readTelegramNumericValue(
      result?.voters
      || result?.count
      || result?.votes
      || result?.votersCount
      || 0
    ) || 0));
    if (
      isTelegramTruthyFlag(result?.chosen)
      || isTelegramTruthyFlag(result?.my)
      || isTelegramTruthyFlag(result?.selected)
      || isTelegramTruthyFlag(result?.self)
      || isTelegramTruthyFlag(result?.mine)
      || typeof result?.chosenOrder !== 'undefined'
      || typeof result?.selectedOrder !== 'undefined'
    ) {
      chosenOptionIds.add(id);
    }
    resultById.set(id, {
      voteCount: voters,
      correct: result?.correct === true
    });
  });
  [
    results?.chosenOption,
    results?.chosenOptions,
    results?.chosenOptionIds,
    results?.selectedOption,
    results?.selectedOptions,
    results?.selectedOptionIds,
    results?.myOption,
    results?.myOptions,
    results?.myVote,
    results?.myVotes
  ].forEach((candidate) => {
    const values = Array.isArray(candidate) ? candidate : [candidate];
    values.forEach((value, index) => {
      if (value == null || typeof value === 'boolean') return;
      const id = resolveKnownPollOptionId(value, index);
      if (id && knownAnswerIds.has(id)) {
        chosenOptionIds.add(id);
      }
    });
  });
  const totalVoters = Math.max(
    0,
    totalVotersHint
    || Array.from(resultById.values()).reduce((sum, item) => (
      sum + Math.max(0, Math.trunc(Number(item?.voteCount || 0) || 0))
    ), 0)
  );

  const optionMap = {};
  const options = answers.map((answer) => {
    const stats = resultById.get(answer.id) || {};
    if (answer.telegramOption) {
      optionMap[answer.id] = answer.telegramOption;
    }
    return {
      ...answer,
      voteCount: Math.max(0, Number(stats.voteCount || 0) || 0),
      percent: totalVoters > 0
        ? Math.max(0, Math.min(100, (Math.max(0, Number(stats.voteCount || 0) || 0) / totalVoters) * 100))
        : 0,
      selected: chosenOptionIds.has(answer.id),
      correct: stats.correct === true
    };
  });
  const closeAtSeconds = Math.max(0, Math.trunc(Number(poll.closeDate || 0) || 0));
  const pollId = cleanTelegramText(
    `telegram-${chatId || 'chat'}-${poll.id || getTelegramMessageId(message) || Date.now()}`.replace(/[^a-z0-9._:-]+/giu, '-'),
    140
  );
  return {
    pollId,
    question,
    description: cleanTelegramMultiline(results?.solution || '', 1200),
    options,
    multiple: poll.multipleChoice === true,
    allowRevote: true,
    showVoters: poll.publicVoters === true,
    shuffleOptions: false,
    correctOptionIds: options.filter((option) => option.correct === true).map((option) => option.id),
    resultsVisibility: 'always',
    closeAt: closeAtSeconds > 0 ? closeAtSeconds * 1000 : 0,
    createdAt: getTelegramMessageTimestamp(message),
    isClosed: poll.closed === true,
    totalVoters,
    currentUserOptionIds: Array.from(chosenOptionIds.values()),
    telegramOptionMap: optionMap
  };
}

function getTelegramNativePollPreview(message = null) {
  const nativePoll = getTelegramNativePollPayload(message);
  if (!nativePoll) return '';
  const question = cleanTelegramMultiline(nativePoll.question || '', 600);
  if (!question) return '';
  const answers = (Array.isArray(nativePoll.options) ? nativePoll.options : [])
    .map((answer, index) => cleanTelegramMultiline(answer?.text || `Вариант ${index + 1}`, 220))
    .filter(Boolean)
    .slice(0, 10);
  const lines = [`Опрос: ${question}`];
  answers.forEach((answer, index) => {
    lines.push(`${index + 1}. ${answer}`);
  });
  return cleanTelegramMultiline(lines.join('\n'), 6000);
}

function getTelegramNativePollPreviewLegacy(message = null) {
  const poll = message?.media?.poll?.poll || message?.poll?.poll || null;
  if (!poll || typeof poll !== 'object') return '';
  const question = cleanTelegramMultiline(getTelegramTextWithEntitiesText(poll.question || poll.title || ''), 600);
  if (!question) return '';
  const answers = (Array.isArray(poll.answers) ? poll.answers : [])
    .map((answer, index) => cleanTelegramMultiline(getTelegramTextWithEntitiesText(answer?.text || answer?.title || `Вариант ${index + 1}`), 220))
    .filter(Boolean)
    .slice(0, 10);
  const lines = [`Опрос: ${question}`];
  answers.forEach((answer, index) => {
    lines.push(`${index + 1}. ${answer}`);
  });
  return cleanTelegramMultiline(lines.join('\n'), 6000);
}

function getTelegramTextWithEntitiesText(value = '') {
  if (value && typeof value === 'object' && !Array.isArray(value)) {
    return cleanTelegramMultiline(value.text || value.value || '', 6000);
  }
  return cleanTelegramMultiline(value || '', 6000);
}

function buildTelegramTextWithEntities(dependency = null, value = '') {
  const text = getTelegramTextWithEntitiesText(value);
  const TextWithEntities = dependency?.Api?.TextWithEntities;
  if (typeof TextWithEntities !== 'function') return text;
  return new TextWithEntities({
    text,
    entities: []
  });
}

function getTelegramReactionDisplayEmoji(value = null) {
  if (!value) return '';
  const normalizePresentation = (emoji = '') => {
    const raw = cleanTelegramText(emoji, 16);
    const withoutTextPresentation = raw.replace(/\uFE0E/gu, '');
    return withoutTextPresentation === '\u2764' ? '\u2764\uFE0F' : raw;
  };
  if (typeof value === 'string') {
    return normalizePresentation(value);
  }
  const nested = value?.reaction && typeof value.reaction === 'object'
    ? getTelegramReactionDisplayEmoji(value.reaction)
    : '';
  return normalizePresentation(
    value?.emoji
    || value?.emoticon
    || value?.reactionEmoji
    || value?.reactionValue
    || nested
    || ''
  );
}

function normalizeTelegramMessageReactions(message = null) {
  const source = message?.reactions && typeof message.reactions === 'object'
    ? message.reactions
    : null;
  if (!source) return [];

  const selfReactedEmoji = new Set();
  (Array.isArray(source.results) ? source.results : []).forEach((result) => {
    const emoji = getTelegramReactionDisplayEmoji(result?.reaction || result);
    if (!emoji) return;
    if (typeof result?.chosenOrder !== 'undefined' && result.chosenOrder !== null) {
      selfReactedEmoji.add(emoji);
    }
  });
  (Array.isArray(source.recentReactions) ? source.recentReactions : []).forEach((reaction) => {
    const emoji = getTelegramReactionDisplayEmoji(reaction?.reaction || reaction);
    if (emoji && reaction?.my === true) {
      selfReactedEmoji.add(emoji);
    }
  });

  return (Array.isArray(source.results) ? source.results : [])
    .map((result) => {
      const emoji = getTelegramReactionDisplayEmoji(result?.reaction || result);
      const count = Math.max(0, Math.trunc(Number(result?.count || 0) || 0));
      if (!emoji || count <= 0) return null;
      const selfReacted = selfReactedEmoji.has(emoji);
      const memberIds = selfReacted ? ['telegram:self'] : [];
      return {
        emoji,
        count,
        selfReacted,
        self: selfReacted,
        isMine: selfReacted,
        mine: selfReacted,
        my: selfReacted,
        selected: selfReacted,
        ...(memberIds.length ? { memberIds } : {})
      };
    })
    .filter(Boolean);
}

function normalizeTelegramMessage(message = null, chatId = '', settings = null) {
  if (!message || typeof message !== 'object') return null;
  const id = getTelegramMessageId(message);
  if (!id) return null;
  const timestamp = getTelegramMessageTimestamp(message);
  const phoneCallPresentation = buildTelegramPhoneCallActionPresentation(message);
  const bodyText = cleanTelegramMultiline(message.message || message.text || '', 6000);
  const formattedBodyText = formatTelegramMessageTextWithEntities(message, bodyText);
  const nativePoll = getTelegramNativePollPayload(message, chatId);
  const nativePollPreview = getTelegramNativePollPreview(message);
  const text = phoneCallPresentation?.text || bodyText || nativePollPreview;
  const formattedText = phoneCallPresentation?.formattedText || formattedBodyText || nativePollPreview;
  const author = getTelegramMessageAuthor(message);
  const attachments = normalizeTelegramMessageAttachments(message, chatId, settings);
  const telegramLinks = extractTelegramMessageEntityLinks(message, text);
  const reactions = normalizeTelegramMessageReactions(message);
  const mediaAttachmentLabel = attachments.length === 1
    ? attachments[0].name
    : (attachments.length > 1 ? `Вложения (${attachments.length})` : '');
  const attachmentLabel = phoneCallPresentation?.attachmentLabel || mediaAttachmentLabel;
  const content = [];
  if (formattedText) {
    content.push({ markdown: formattedText });
  }
  if (attachments.length) {
    content.push({ attachments });
  }
  if (nativePoll) {
    content.push({ poll: nativePoll });
  }
  const forwardedSource = getTelegramForwardedSource(message);
  const raw = {
    id,
    messageId: id,
    text,
    formattedText,
    createdAt: timestamp,
    isMine: message.out === true,
    authorName: author.name,
    authorMemberId: author.memberId,
    inReplyToMessageId: getTelegramReplyToMessageId(message),
    content,
    attachments,
    attachmentLabel,
    telegramLinks,
    nativePoll,
    source: 'telegram',
    systemSignal: phoneCallPresentation?.systemSignal || '',
    telegramCall: phoneCallPresentation ? {
      callId: phoneCallPresentation.callId,
      reason: phoneCallPresentation.reason,
      durationSeconds: phoneCallPresentation.durationSeconds,
      video: phoneCallPresentation.video,
      outgoing: phoneCallPresentation.outgoing
    } : null,
    callDurationSeconds: phoneCallPresentation?.durationSeconds || 0
  };
  if (reactions.length) {
    raw.reactions = reactions;
  }
  if (forwardedSource) {
    raw.forwardedSource = forwardedSource;
  }
  return {
    id,
    workspaceId: 'telegram',
    chatId: normalizeTelegramChatId(chatId),
    text: text || attachmentLabel || 'Сообщение',
    formattedText,
    authorName: author.name,
    authorMemberId: author.memberId,
    authorAvatarUrl: '',
    timestamp,
    isMine: message.out === true,
    isSystem: Boolean(phoneCallPresentation),
    deliveryStatus: message.out === true ? 'sent' : '',
    readByMemberIds: [],
    replyToMessageId: getTelegramReplyToMessageId(message),
    threadChatId: '',
    threadTitle: '',
    threadMessageCount: 0,
    forwardedSource,
    nativePoll,
    attachments,
    telegramLinks,
    reactions,
    raw
  };
}

function normalizeTelegramMessageList(messages = [], chatId = '', settings = null) {
  return (Array.isArray(messages) ? messages : Array.from(messages || []))
    .map((message) => normalizeTelegramMessage(message, chatId, settings))
    .filter(Boolean)
    .sort((left, right) => Number(left.timestamp || 0) - Number(right.timestamp || 0));
}

function buildTelegramErrorPayload(error = null, fallbackCode = 'TELEGRAM_ERROR') {
  const rawCode = cleanTelegramText(error?.errorMessage || error?.code || fallbackCode, 80).toUpperCase();
  let message = cleanTelegramText(
    error?.message || error?.errorMessage || 'Не удалось выполнить запрос Telegram.',
    300
  ) || 'Не удалось выполнить запрос Telegram.';
  const passwordRequired = rawCode === 'SESSION_PASSWORD_NEEDED' || /SESSION_PASSWORD_NEEDED/iu.test(message);
  if (rawCode === 'TELEGRAM_FAKE_TLS_PROXY_UNSUPPORTED') {
    message = cleanTelegramText(error?.message || 'Этот MTProxy начинается с ee, но Fake TLS transport недоступен в текущей сборке.', 420);
  } else if (rawCode === 'TELEGRAM_CONNECT_FAILED') {
    message = cleanTelegramText(error?.message || 'Telegram не смог создать MTProto-сессию через этот прокси. Код не отправлен.', 420);
  } else if (rawCode === 'TELEGRAM_TIMEOUT') {
    message = cleanTelegramText(error?.message || 'Telegram не ответил вовремя. Проверьте API-настройки и MTProxy.', 300);
  } else if (/MTProxy secret must be a hex-string representing 16 bytes/iu.test(message)) {
    message = 'Не удалось подготовить MTProxy secret. Проверьте ссылку Telegram proxy.';
  }
  return {
    ok: false,
    code: passwordRequired ? 'TELEGRAM_PASSWORD_REQUIRED' : rawCode,
    error: passwordRequired ? 'Введите пароль двухфакторной защиты Telegram.' : message,
    passwordRequired,
    webFallbackAvailable: false
  };
}

async function getTelegramIntegrationState(payload = {}) {
  const settings = normalizeTelegramApiSettings(payload?.settings || payload);
  const validation = validateTelegramApiSettings(settings);
  const dependency = getTelegramDependency();
  const hasSession = Boolean(getStoredTelegramSessionString());
  let authorized = false;
  let connected = false;
  let self = null;
  if (dependency.ok && validation.ok && settings.enabled && settings.apiId && settings.apiHash && hasSession) {
    try {
      const { client } = await ensureTelegramClient(settings);
      connected = true;
      authorized = await withTelegramTimeout(
        client.checkAuthorization(),
        TELEGRAM_CONNECT_TIMEOUT_MS,
        'Проверка авторизации Telegram'
      ).catch(() => false);
      if (authorized) {
        self = await resolveTelegramSelfParticipant(client, settings).catch(() => null);
      }
      saveTelegramClientSession(client);
    } catch {
      connected = false;
      authorized = false;
      self = null;
    }
  }
  return {
    ok: true,
    enabled: settings.enabled,
    dependencyAvailable: dependency.ok,
    dependencyError: dependency.ok ? '' : dependency.error,
    configured: Boolean(settings.phoneNumber || hasSession),
    credentialsAvailable: Boolean(settings.apiId && settings.apiHash),
    apiSource: settings.apiSource || '',
    proxyValid: validation.ok,
    proxyError: validation.ok ? '' : validation.error,
    proxyLabel: validation.proxyLabel || '',
    proxyMode: validation.proxyMode || '',
    fakeTlsDomain: validation.fakeTlsDomain || '',
    proxySupportedByClient: validation.ok,
    hasSession,
    hasWebSession: false,
    webMode: false,
    webFallbackAvailable: false,
    connected,
    authorized,
    self
  };
}

async function connectTelegramIntegration(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const preferWebBridge = payload?.webBridge === true || payload?.webMode === true || payload?.webFallback === true;
    if (shouldUseTelegramWebBridge(settings) || preferWebBridge) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_DISABLED',
        error: 'Telegram Web отключён. Используйте API Telegram и MTProxy.',
        webMode: false
      };
    }
    const { client, proxyLabel, proxyMode, fakeTlsDomain } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    saveTelegramClientSession(client);
    return {
      ok: true,
      connected: true,
      authorized,
      proxyLabel: proxyLabel || '',
      proxyMode: proxyMode || '',
      fakeTlsDomain: fakeTlsDomain || '',
      hasSession: Boolean(getStoredTelegramSessionString())
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_CONNECT_ERROR');
  }
}

async function sendTelegramCode(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    if (shouldUseTelegramWebBridge(settings)) {
      return {
        ok: false,
        code: 'TELEGRAM_PROXY_UNSUPPORTED',
        error: 'Эта сборка использует только Telegram API и MTProxy. Telegram Web отключён.',
        webMode: false
      };
    }
    const phoneNumber = cleanTelegramText(payload?.phoneNumber || settings.phoneNumber || '', 64);
    if (!phoneNumber) {
      throw Object.assign(new Error('Укажите номер телефона Telegram.'), {
        code: 'TELEGRAM_PHONE_MISSING'
      });
    }
    const { client, proxyLabel, proxyMode, fakeTlsDomain } = await ensureTelegramClient(settings, {
      ignoreStoredSession: true
    });
    const sendCodeResultPromise = client.sendCode({
      apiId: settings.apiId,
      apiHash: settings.apiHash
    }, phoneNumber, payload?.forceSMS === true).then((result) => {
      telegramPendingAuth = {
        phoneNumber,
        phoneCodeHash: cleanTelegramText(result?.phoneCodeHash || '', 256),
        isCodeViaApp: result?.isCodeViaApp === true,
        createdAt: Date.now()
      };
      if (!telegramPendingAuth.phoneCodeHash) {
        throw Object.assign(new Error('Telegram не вернул phone_code_hash.'), {
          code: 'TELEGRAM_CODE_HASH_MISSING'
        });
      }
      saveTelegramClientSession(client);
      return telegramPendingAuth;
    });
    let trackedSendCodePromise = null;
    trackedSendCodePromise = sendCodeResultPromise.finally(() => {
      if (telegramPendingAuthPromise === trackedSendCodePromise) {
        telegramPendingAuthPromise = null;
      }
    });
    telegramPendingAuthPromise = trackedSendCodePromise;
    const pendingAuth = await withTelegramTimeout(
      trackedSendCodePromise,
      TELEGRAM_SEND_CODE_TIMEOUT_MS,
      'Отправка кода Telegram'
    );
    return {
      ok: true,
      codeSent: true,
      isCodeViaApp: pendingAuth.isCodeViaApp,
      proxyLabel: proxyLabel || '',
      proxyMode: proxyMode || '',
      fakeTlsDomain: fakeTlsDomain || ''
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_SEND_CODE_ERROR');
  }
}

async function signInTelegramIntegration(payload = {}) {
  try {
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(`GramJS недоступен: ${dependency.error}`), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const phoneNumber = cleanTelegramText(payload?.phoneNumber || settings.phoneNumber || telegramPendingAuth?.phoneNumber || '', 64);
    const code = cleanTelegramText(payload?.code || payload?.phoneCode || '', 64).replace(/\s+/gu, '');
    const password = String(payload?.password || '').trim();
    const { client } = await ensureTelegramClient(settings);

    if (!telegramPendingAuth?.phoneCodeHash && telegramPendingAuthPromise) {
      await withTelegramTimeout(
        telegramPendingAuthPromise.catch(() => null),
        12000,
        'Ожидание ответа Telegram по коду'
      ).catch(() => null);
    }

    if (password && (!code || !telegramPendingAuth?.phoneCodeHash)) {
      await withTelegramTimeout(
        client.signInWithPassword({
          apiId: settings.apiId,
          apiHash: settings.apiHash
        }, {
          password: async () => password,
          onError: (error) => {
            throw error;
          }
        }),
        TELEGRAM_SIGN_IN_TIMEOUT_MS,
        'Проверка пароля Telegram'
      );
      saveTelegramClientSession(client);
      telegramPendingAuth = null;
      return { ok: true, authorized: true };
    }

    if (!phoneNumber || !code || !telegramPendingAuth?.phoneCodeHash) {
      throw Object.assign(new Error('Сначала отправьте код Telegram, затем введите его.'), {
        code: 'TELEGRAM_CODE_MISSING'
      });
    }

    let result = null;
    try {
      result = await withTelegramTimeout(
        client.invoke(new dependency.Api.auth.SignIn({
          phoneNumber,
          phoneCodeHash: telegramPendingAuth.phoneCodeHash,
          phoneCode: code
        })),
        TELEGRAM_SIGN_IN_TIMEOUT_MS,
        'Проверка кода Telegram'
      );
    } catch (error) {
      const rawCode = cleanTelegramText(error?.errorMessage || error?.code || '', 120).toUpperCase();
      if (rawCode === 'SESSION_PASSWORD_NEEDED') {
        if (!password) {
          return {
            ok: false,
            code: 'TELEGRAM_PASSWORD_REQUIRED',
            error: 'Введите пароль двухфакторной защиты Telegram.',
            passwordRequired: true
          };
        }
        await withTelegramTimeout(
          client.signInWithPassword({
            apiId: settings.apiId,
            apiHash: settings.apiHash
          }, {
            password: async () => password,
            onError: (passwordError) => {
              throw passwordError;
            }
          }),
          TELEGRAM_SIGN_IN_TIMEOUT_MS,
          'Проверка пароля Telegram'
        );
        saveTelegramClientSession(client);
        telegramPendingAuth = null;
        return { ok: true, authorized: true };
      }
      throw error;
    }

    if (result instanceof dependency.Api.auth.AuthorizationSignUpRequired) {
      throw Object.assign(new Error('Для новых Telegram-аккаунтов регистрация из YuChat пока не поддерживается.'), {
        code: 'TELEGRAM_SIGNUP_REQUIRED'
      });
    }

    saveTelegramClientSession(client);
    telegramPendingAuth = null;
    return { ok: true, authorized: true };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_SIGN_IN_ERROR');
  }
}

async function listTelegramDialogs(payload = {}) {
  const settings = normalizeTelegramApiSettings(payload?.settings || payload);
  const preferWebBridge = payload?.webBridge === true || payload?.webMode === true || payload?.webFallback === true;
  try {
    if (shouldUseTelegramWebBridge(settings) || preferWebBridge) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_DISABLED',
        error: 'Telegram Web отключён. Диалоги загружаются только через Telegram API и MTProxy.',
        authorized: false,
        webMode: false
      };
    }
    const { client, proxyLabel } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Отправьте код и выполните вход.',
        authorized: false
      };
    }
    const limit = Math.max(1, Math.min(200, Math.trunc(Number(payload?.limit || TELEGRAM_DEFAULT_DIALOG_LIMIT) || TELEGRAM_DEFAULT_DIALOG_LIMIT)));
    const dialogResults = await Promise.allSettled([
      withTelegramTimeout(
        client.getDialogs({ limit }),
        TELEGRAM_DIALOGS_TIMEOUT_MS,
        'Загрузка диалогов Telegram'
      ),
      withTelegramTimeout(
        client.getDialogs({ limit, archived: true }),
        TELEGRAM_DIALOGS_TIMEOUT_MS,
        'Загрузка архива Telegram'
      )
    ]);
    if (dialogResults[0]?.status === 'rejected' && dialogResults[1]?.status === 'rejected') {
      throw dialogResults[0].reason || dialogResults[1].reason;
    }
    const activeDialogs = dialogResults[0]?.status === 'fulfilled'
      ? (Array.isArray(dialogResults[0].value) ? dialogResults[0].value : Array.from(dialogResults[0].value || []))
      : [];
    const archivedDialogs = dialogResults[1]?.status === 'fulfilled'
      ? (Array.isArray(dialogResults[1].value) ? dialogResults[1].value : Array.from(dialogResults[1].value || []))
      : [];
    const pairsByChatId = new Map();
    [
      ...activeDialogs.map((dialog) => ({ dialog, archived: false })),
      ...archivedDialogs.map((dialog) => ({ dialog, archived: true }))
    ].forEach(({ dialog, archived }) => {
      const normalized = normalizeTelegramDialog(dialog, settings, { archived });
      if (!normalized) return;
      const existing = pairsByChatId.get(normalized.chatId) || null;
      if (!existing) {
        rememberTelegramDialogEntity(dialog, normalized);
        pairsByChatId.set(normalized.chatId, { dialog, normalized });
        return;
      }
      const shouldReplace = (
        existing.normalized?.isArchived === true && normalized.isArchived !== true
      ) || (
        Number(normalized.updatedAt || 0) > Number(existing.normalized?.updatedAt || 0)
      );
      if (shouldReplace) {
        rememberTelegramDialogEntity(dialog, normalized);
        pairsByChatId.set(normalized.chatId, { dialog, normalized });
        return;
      }
      existing.normalized.isArchived = existing.normalized.isArchived === true && normalized.isArchived === true;
    });
    const pairs = Array.from(pairsByChatId.values()).filter(Boolean);
    await hydrateTelegramDialogPeerState(pairs, client).catch(() => null);
    await hydrateTelegramDialogAvatarDataUrls(pairs, client);
    await hydrateTelegramDialogPreviewAuthorData(pairs, client, settings);
    await hydrateTelegramDialogProfileDetails(pairs, client).catch(() => null);
    const self = await resolveTelegramSelfParticipant(client, settings).catch(() => null);
    const items = pairs.map((pair) => pair.normalized).filter(Boolean);
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      proxyLabel: proxyLabel || '',
      self,
      dialogs: items,
      loadedAt: Date.now()
    };
  } catch (error) {
    if (preferWebBridge) {
      const fallback = await scrapeTelegramWebDialogs(payload, {
        showWindow: false,
        attempts: 5
      }).catch(() => null);
      if (fallback && typeof fallback === 'object') {
        return fallback;
      }
    }
    return buildTelegramErrorPayload(error, 'TELEGRAM_DIALOGS_ERROR');
  }
}

async function listTelegramMessages(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return await listTelegramWebMessages(payload);
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) {
      throw Object.assign(new Error('Не удалось определить Telegram-диалог.'), {
        code: 'TELEGRAM_PEER_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const count = Math.max(1, Math.min(200, Math.trunc(Number(payload?.count || payload?.limit || 50) || 50)));
    const messages = await withTelegramTimeout(
      client.getMessages(entity, { limit: count }),
      TELEGRAM_MESSAGES_TIMEOUT_MS,
      'Загрузка сообщений Telegram'
    );
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      items: normalizeTelegramMessageList(messages, chatId, settings),
      hasMore: Array.from(messages || []).length >= count,
      loadedCount: count,
      resolvedChatId: chatId,
      resolvedWorkspaceId: 'telegram'
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_MESSAGES_ERROR');
  }
}

async function listTelegramParticipants(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: true,
        authorized: true,
        participants: [],
        resolvedChatId: chatId,
        resolvedWorkspaceId: 'telegram'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) {
      throw Object.assign(new Error('Не удалось определить Telegram-диалог.'), {
        code: 'TELEGRAM_PEER_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const limit = Math.max(1, Math.min(300, Math.trunc(Number(payload?.limit || 160) || 160)));
    let users = [];
    const entityLooksLikeUser = Boolean(
      entity
      && typeof entity === 'object'
      && (
        entity.firstName
        || entity.lastName
        || entity.username
        || /User/iu.test(cleanTelegramText(entity.className || entity.constructor?.name || '', 80))
      )
      && !entity.title
    );
    if (entityLooksLikeUser) {
      users = [entity];
    } else if (typeof client.getParticipants === 'function') {
      users = await withTelegramTimeout(
        client.getParticipants(entity, { limit }),
        TELEGRAM_MESSAGES_TIMEOUT_MS,
        'Загрузка участников Telegram'
      ).catch(() => []);
    }
    const seen = new Set();
    const pairs = (Array.isArray(users) ? users : Array.from(users || []))
      .map((user) => {
        const normalized = normalizeTelegramParticipant(user, settings);
        if (!normalized || seen.has(normalized.memberId)) return null;
        seen.add(normalized.memberId);
        return { user, normalized };
      })
      .filter(Boolean);
    await hydrateTelegramParticipantAvatarDataUrls(pairs, client);
    await hydrateTelegramParticipantDetails(pairs, client, {
      limit: entityLooksLikeUser ? 1 : 40
    }).catch(() => null);
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      participants: pairs.map((pair) => pair.normalized).filter(Boolean),
      resolvedChatId: chatId,
      resolvedWorkspaceId: 'telegram',
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_PARTICIPANTS_ERROR');
  }
}

async function listTelegramMessageReadReceipts(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    const messageId = Math.trunc(Number(payload?.messageId || payload?.msgId || 0) || 0);
    if (!chatId || messageId <= 0) {
      throw Object.assign(new Error('Не удалось определить Telegram-сообщение.'), {
        code: 'TELEGRAM_MESSAGE_MISSING'
      });
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) {
      throw Object.assign(new Error('Не удалось определить Telegram-диалог.'), {
        code: 'TELEGRAM_PEER_MISSING'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(`GramJS недоступен: ${dependency.error}`), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const rows = await withTelegramTimeout(
      client.invoke(new dependency.Api.messages.GetMessageReadParticipants({
        peer: entity,
        msgId: messageId
      })),
      TELEGRAM_MESSAGES_TIMEOUT_MS,
      'Загрузка прочитавших Telegram'
    ).catch(() => []);
    const safeRows = Array.isArray(rows) ? rows : Array.from(rows || []);
    const participants = [];
    const seen = new Set();
    for (const row of safeRows) {
      const rawUserId = normalizeTelegramPeerId(row?.userId || row?.user_id || '');
      if (!rawUserId || seen.has(rawUserId)) continue;
      seen.add(rawUserId);
      let user = null;
      try {
        user = await withTelegramTimeout(
          client.getEntity(rawUserId),
          Math.min(TELEGRAM_MESSAGES_TIMEOUT_MS, 6000),
          'Загрузка профиля прочитавшего Telegram'
        );
      } catch {
        user = { id: rawUserId, firstName: `Telegram ${rawUserId}` };
      }
      const normalized = normalizeTelegramParticipant(user || { id: rawUserId }, settings) || {
        id: `telegram:${rawUserId}`,
        memberId: `telegram:${rawUserId}`,
        peerId: rawUserId,
        label: `Telegram ${rawUserId}`,
        title: `Telegram ${rawUserId}`,
        avatarUrl: ''
      };
      participants.push({
        ...normalized,
        readAt: normalizeTelegramEpochSeconds(row?.date || 0) * 1000
      });
      if (participants.length >= 60) break;
    }
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      participants,
      resolvedChatId: chatId,
      resolvedWorkspaceId: 'telegram',
      messageId: String(messageId)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_READ_RECEIPTS_ERROR');
  }
}

async function resolveTelegramUsername(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const username = cleanTelegramText(payload?.username || payload?.mention || '', 120).replace(/^@+/u, '');
    if (!/^[A-Za-z0-9_]{3,64}$/u.test(username)) {
      return {
        ok: false,
        code: 'TELEGRAM_USERNAME_INVALID',
        error: 'Некорректное имя пользователя Telegram.'
      };
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await withTelegramTimeout(
      client.getEntity(`@${username}`),
      TELEGRAM_MESSAGES_TIMEOUT_MS,
      'Поиск пользователя Telegram'
    );
    const normalized = normalizeTelegramParticipant(entity, settings);
    if (!normalized) {
      return {
        ok: false,
        code: 'TELEGRAM_USERNAME_NOT_FOUND',
        error: 'Пользователь Telegram не найден.'
      };
    }
    const pairs = [{ user: entity, normalized }];
    await hydrateTelegramParticipantAvatarDataUrls(pairs, client);
    await hydrateTelegramParticipantDetails(pairs, client, { limit: 1 }).catch(() => null);
    rememberTelegramEntity(`@${username}`, entity);
    rememberTelegramEntity(normalized.memberId, entity);
    rememberTelegramEntity(normalized.peerId, entity);
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      participant: normalized,
      resolvedWorkspaceId: 'telegram'
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_USERNAME_RESOLVE_ERROR');
  }
}

function normalizeTelegramCommonChat(chat = null, settings = null) {
  if (!chat || typeof chat !== 'object') return null;
  const id = normalizeTelegramPeerId(chat.id || chat.chatId || chat.channelId || '');
  if (!id) return null;
  const title = cleanTelegramText(chat.title || chat.name || `Telegram ${id}`, 180) || `Telegram ${id}`;
  const className = cleanTelegramText(chat.className || chat.constructor?.name || '', 120);
  const type = /Channel/iu.test(className) && chat.megagroup !== true ? 'channel' : 'group';
  const avatarCacheKey = buildTelegramAvatarCacheKey(chat, id);
  const avatarResourceUrl = rememberTelegramAvatarRecord(chat, id, settings, chat.inputEntity || null);
  const cachedAvatarUrl = getCachedTelegramAvatarDataUrl(avatarCacheKey);
  return {
    id,
    chatId: `tg:${id}`,
    title,
    type,
    username: cleanTelegramText(chat.username || '', 120),
    avatarUrl: cachedAvatarUrl,
    avatarCacheKey,
    avatarResourceUrl,
    memberCount: Math.max(0, Math.trunc(Number(chat.participantsCount || chat.participants_count || 0) || 0)),
    unreadCount: 0,
    previewText: '',
    previewTimestamp: 0,
    updatedAt: 0,
    isTelegram: true
  };
}

async function hydrateTelegramCommonChatAvatarDataUrls(pairs = [], client = null) {
  const sourcePairs = (Array.isArray(pairs) ? pairs : [])
    .filter((pair) => pair?.normalized && hasTelegramProfilePhoto(pair?.chat))
    .slice(0, TELEGRAM_DIALOG_AVATAR_LIMIT);
  if (!sourcePairs.length || !client) return;
  await Promise.allSettled(sourcePairs.map(async (pair) => {
    const body = await downloadTelegramProfilePhoto(client, {
      entity: pair.chat || null,
      inputEntity: pair.chat?.inputEntity || null,
      avatarCacheKey: pair.normalized?.avatarCacheKey || '',
      peerId: pair.normalized?.id || '',
      chatId: pair.normalized?.chatId || ''
    }).catch(() => Buffer.alloc(0));
    const dataUrl = buildTelegramAvatarDataUrl(body);
    if (dataUrl) {
      pair.normalized.avatarUrl = dataUrl;
    }
  }));
}

async function listTelegramCommonChats(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) {
      throw Object.assign(new Error('Не удалось определить Telegram-контакт.'), {
        code: 'TELEGRAM_PEER_MISSING'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(`GramJS недоступен: ${dependency.error}`), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const limit = Math.max(1, Math.min(120, Math.trunc(Number(payload?.limit || 60) || 60)));
    const response = await withTelegramTimeout(
      client.invoke(new dependency.Api.messages.GetCommonChats({
        userId: entity,
        maxId: 0,
        limit
      })),
      TELEGRAM_MESSAGES_TIMEOUT_MS,
      'Загрузка общих групп Telegram'
    );
    const pairs = (Array.isArray(response?.chats) ? response.chats : [])
      .map((chat) => {
        const normalized = normalizeTelegramCommonChat(chat, settings);
        if (!normalized) return null;
        rememberTelegramEntity(normalized.chatId, chat);
        rememberTelegramEntity(normalized.id, chat);
        return { chat, normalized };
      })
      .filter(Boolean);
    await hydrateTelegramCommonChatAvatarDataUrls(pairs, client);
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      groups: pairs.map((pair) => pair.normalized).filter(Boolean),
      resolvedChatId: chatId,
      resolvedWorkspaceId: 'telegram',
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_COMMON_CHATS_ERROR');
  }
}

async function createTelegramChannel(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const title = cleanTelegramText(payload?.title || payload?.name || '', 140);
    const about = cleanTelegramMultiline(payload?.about || payload?.description || '', 900);
    if (!title) {
      throw Object.assign(new Error('Укажите название Telegram-канала.'), {
        code: 'TELEGRAM_CHANNEL_TITLE_MISSING'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(`GramJS недоступен: ${dependency.error}`), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const response = await withTelegramTimeout(
      client.invoke(new dependency.Api.channels.CreateChannel({
        title,
        about,
        broadcast: true,
        megagroup: false
      })),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Создание Telegram-канала'
    );
    const chats = Array.isArray(response?.chats) ? response.chats : [];
    const createdChat = chats.find((chat) => cleanTelegramText(chat?.title || '', 180) === title)
      || chats[0]
      || response?.chat
      || response?.channel
      || null;
    const normalized = normalizeTelegramCommonChat(createdChat, settings);
    if (!normalized) {
      throw Object.assign(new Error('Telegram создал канал, но не вернул его карточку.'), {
        code: 'TELEGRAM_CHANNEL_RESPONSE_INVALID'
      });
    }
    normalized.previewText = 'Канал создан';
    normalized.previewTimestamp = Date.now();
    normalized.updatedAt = normalized.previewTimestamp;
    normalized.isArchived = false;
    rememberTelegramEntity(normalized.chatId, createdChat);
    rememberTelegramEntity(normalized.id, createdChat);
    await hydrateTelegramCommonChatAvatarDataUrls([{ chat: createdChat, normalized }], client).catch(() => null);
    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      channel: normalized,
      dialog: normalized,
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_CHANNEL_CREATE_ERROR');
  }
}

function normalizeTelegramReplyToId(value = '') {
  const raw = cleanTelegramText(value || '', 80);
  if (!raw || /^optimistic-/iu.test(raw)) return 0;
  const numeric = Number(raw);
  return Number.isSafeInteger(numeric) && numeric > 0 ? numeric : 0;
}

async function sendTelegramMessage(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return await sendTelegramWebMessage(payload);
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const text = cleanTelegramMultiline(payload?.text || payload?.message || '', 6000);
    if (!peerId || !text) {
      throw Object.assign(new Error('Не удалось отправить пустое Telegram-сообщение.'), {
        code: 'TELEGRAM_MESSAGE_EMPTY'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const replyTo = normalizeTelegramReplyToId(payload?.inReplyToMessageId || payload?.replyToMessageId || '');
    const message = await withTelegramTimeout(
      client.sendMessage(entity, {
        message: text,
        replyTo: replyTo || undefined,
        linkPreview: true,
        schedule: normalizeTelegramScheduleDate(payload?.scheduledAt || payload?.scheduleDate || 0) || undefined
      }),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Отправка сообщения Telegram'
    );
    saveTelegramClientSession(client);
    return {
      ok: true,
      message: normalizeTelegramMessage(message, chatId, settings)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_SEND_ERROR');
  }
}

function normalizeTelegramPollSendPayload(payload = {}) {
  const source = isPlainRecord(payload?.poll) ? payload.poll : payload;
  const question = cleanTelegramMultiline(source?.question || source?.title || '', 300);
  const description = cleanTelegramMultiline(source?.description || source?.caption || '', 900);
  const rawOptions = Array.isArray(source?.options) ? source.options : [];
  const options = rawOptions
    .map((option, index) => ({
      id: cleanTelegramText(option?.id || `opt-${index + 1}`, 80) || `opt-${index + 1}`,
      text: cleanTelegramMultiline(option?.text || option?.title || '', 100).replace(/\s+/gu, ' ').trim()
    }))
    .filter((option) => option.text)
    .slice(0, 10);
  const correctOptionIdSet = new Set(
    (Array.isArray(source?.correctOptionIds) ? source.correctOptionIds : [])
      .map((id) => cleanTelegramText(id || '', 80))
      .filter(Boolean)
  );
  const closeAt = Math.max(0, Number(source?.closeAt || 0) || 0);
  if (!question || options.length < 2) {
    const error = new Error('Для Telegram-опроса нужны вопрос и минимум два варианта.');
    error.code = 'TELEGRAM_POLL_INVALID';
    throw error;
  }
  return {
    question,
    description,
    options,
    multiple: source?.multiple === true,
    showVoters: source?.showVoters === true,
    quiz: source?.quizMode === true && correctOptionIdSet.size > 0,
    correctOptionIdSet,
    closeAt
  };
}

function normalizeTelegramScheduleDate(value = 0) {
  const numeric = Number(value || 0);
  if (!Number.isFinite(numeric) || numeric <= 0) return 0;
  const seconds = numeric > 100000000000 ? Math.floor(numeric / 1000) : Math.floor(numeric);
  const nowSeconds = Math.floor(Date.now() / 1000);
  return seconds > nowSeconds + 30 ? seconds : 0;
}

async function sendTelegramPoll(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_POLL_UNSUPPORTED',
        error: 'Опросы через Telegram Web bridge недоступны.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) {
      throw Object.assign(new Error('Не удалось определить Telegram-диалог.'), {
        code: 'TELEGRAM_PEER_MISSING'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const pollPayload = normalizeTelegramPollSendPayload(payload?.poll || payload);
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const optionBuffersById = new Map();
    const answers = pollPayload.options.map((option, index) => {
      const optionBuffer = Buffer.from([index + 1]);
      optionBuffersById.set(option.id, optionBuffer);
      return new dependency.Api.PollAnswer({
        text: buildTelegramTextWithEntities(dependency, option.text),
        option: optionBuffer
      });
    });
    const correctAnswers = pollPayload.quiz
      ? pollPayload.options
        .map((option) => pollPayload.correctOptionIdSet.has(option.id) ? optionBuffersById.get(option.id) : null)
        .filter(Boolean)
      : [];
    const nowSeconds = Math.floor(Date.now() / 1000);
    const closeDate = pollPayload.closeAt > Date.now() + 5000
      ? Math.floor(pollPayload.closeAt / 1000)
      : 0;
    const poll = new dependency.Api.Poll({
      id: typeof dependency.Helpers?.generateRandomLong === 'function'
        ? dependency.Helpers.generateRandomLong()
        : BigInt(Date.now()) * 1000n + BigInt(crypto.randomInt(0, 999)),
      question: buildTelegramTextWithEntities(dependency, pollPayload.question),
      answers,
      publicVoters: pollPayload.showVoters,
      multipleChoice: pollPayload.multiple,
      quiz: pollPayload.quiz,
      ...(closeDate > nowSeconds ? { closeDate } : {})
    });
    const media = new dependency.Api.InputMediaPoll({
      poll,
      ...(correctAnswers.length ? { correctAnswers } : {}),
      ...(pollPayload.quiz && pollPayload.description ? { solution: pollPayload.description } : {})
    });
    const replyTo = normalizeTelegramReplyToId(payload?.inReplyToMessageId || payload?.replyToMessageId || '');
    const request = new dependency.Api.messages.SendMedia({
      peer: entity,
      media,
      message: pollPayload.quiz ? '' : pollPayload.description,
      randomId: typeof dependency.Helpers?.generateRandomLong === 'function'
        ? dependency.Helpers.generateRandomLong()
        : BigInt(Date.now()) * 100000n + BigInt(crypto.randomInt(0, 99999)),
      replyTo: replyTo
        ? new dependency.Api.InputReplyToMessage({ replyToMsgId: replyTo })
        : undefined,
      scheduleDate: normalizeTelegramScheduleDate(payload?.scheduledAt || payload?.scheduleDate || 0) || undefined
    });
    const result = await withTelegramTimeout(
      client.invoke(request),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Отправка опроса Telegram'
    );
    saveTelegramClientSession(client);
    const messages = Array.isArray(result?.updates)
      ? result.updates.map((update) => update?.message).filter(Boolean)
      : [];
    const message = messages[messages.length - 1] || result?.message || null;
    return {
      ok: true,
      message: normalizeTelegramMessage(message, chatId, settings)
        || {
          id: cleanTelegramText(payload?.clientMessageId || `telegram-poll-${Date.now()}`, 120),
          workspaceId: 'telegram',
          chatId: normalizeTelegramChatId(chatId),
          text: getTelegramNativePollPreview({ media: { poll: { poll } } }) || `Опрос: ${pollPayload.question}`,
          formattedText: '',
          authorName: 'Вы',
          authorMemberId: 'telegram:self',
          timestamp: Date.now(),
          isMine: true,
          deliveryStatus: 'sent',
          attachments: [],
          raw: {
            source: 'telegram',
            poll: pollPayload
          }
        }
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_POLL_SEND_ERROR');
  }
}

async function voteTelegramPoll(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_POLL_VOTE_UNSUPPORTED',
        error: 'Голосование через Telegram Web bridge недоступно.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const messageId = normalizeTelegramReplyToId(payload?.messageId || payload?.msgId || payload?.id || '');
    const optionIds = Array.from(new Set(
      (Array.isArray(payload?.optionIds) ? payload.optionIds : [])
        .map((value) => cleanTelegramText(value || '', 120))
        .filter(Boolean)
    ));
    if (!peerId || !messageId) {
      throw Object.assign(new Error('Не удалось определить Telegram-опрос.'), {
        code: 'TELEGRAM_POLL_VOTE_INVALID'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const fetched = await withTelegramTimeout(
      client.getMessages(entity, { ids: messageId }),
      TELEGRAM_MESSAGES_TIMEOUT_MS,
      'Загрузка опроса Telegram'
    );
    const pollMessage = Array.isArray(fetched) ? fetched[0] : fetched?.[0] || fetched || null;
    const nativePoll = getTelegramNativePollPayload(pollMessage, chatId);
    const optionMap = nativePoll?.telegramOptionMap && typeof nativePoll.telegramOptionMap === 'object'
      ? nativePoll.telegramOptionMap
      : {};
    const options = optionIds
      .map((id) => optionMap[id] ? Buffer.from(optionMap[id], 'base64url') : null)
      .filter(Boolean);
    if (optionIds.length && !options.length) {
      throw Object.assign(new Error('Не удалось подготовить варианты Telegram-опроса.'), {
        code: 'TELEGRAM_POLL_OPTIONS_INVALID'
      });
    }
    await withTelegramTimeout(
      client.invoke(new dependency.Api.messages.SendVote({
        peer: entity,
        msgId: messageId,
        options
      })),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Голосование в Telegram-опросе'
    );
    const expectedOptionIds = Array.from(new Set(optionIds))
      .map((value) => cleanTelegramText(value || '', 120))
      .filter(Boolean)
      .sort((left, right) => left.localeCompare(right, 'en'));
    let refreshedMessage = pollMessage;
    for (let attempt = 0; attempt < 4; attempt += 1) {
      const refreshed = await withTelegramTimeout(
        client.getMessages(entity, { ids: messageId }),
        TELEGRAM_MESSAGES_TIMEOUT_MS,
        'Обновление опроса Telegram'
      ).catch(() => null);
      const candidate = Array.isArray(refreshed) ? refreshed[0] : refreshed?.[0] || refreshed || null;
      if (candidate && typeof candidate === 'object') {
        refreshedMessage = candidate;
      }
      const snapshotPoll = getTelegramNativePollPayload(refreshedMessage, chatId);
      if (!snapshotPoll || expectedOptionIds.length < 1) {
        if (attempt >= 1) break;
      } else {
        const selectedOptionIds = Array.from(new Set(
          (Array.isArray(snapshotPoll.currentUserOptionIds) ? snapshotPoll.currentUserOptionIds : [])
            .map((value) => cleanTelegramText(value || '', 120))
            .filter(Boolean)
        )).sort((left, right) => left.localeCompare(right, 'en'));
        const hasExpectedSelection = (
          selectedOptionIds.length === expectedOptionIds.length
          && expectedOptionIds.every((id, index) => id === selectedOptionIds[index])
        );
        if (hasExpectedSelection) {
          break;
        }
      }
      if (attempt < 3) {
        await waitForTelegramMs(160 + attempt * 180);
      }
    }
    saveTelegramClientSession(client);
    return {
      ok: true,
      message: normalizeTelegramMessage(refreshedMessage, chatId, settings)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_POLL_VOTE_ERROR');
  }
}

async function pinTelegramMessage(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_PIN_UNSUPPORTED',
        error: 'Закрепление через Telegram Web bridge недоступно.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const messageId = normalizeTelegramReplyToId(payload?.messageId || payload?.msgId || payload?.id || '');
    if (!peerId || !messageId) {
      throw Object.assign(new Error('Не удалось определить Telegram-сообщение для закрепления.'), {
        code: 'TELEGRAM_PIN_INVALID'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    await withTelegramTimeout(
      client.invoke(new dependency.Api.messages.UpdatePinnedMessage({
        peer: entity,
        id: messageId,
        silent: true,
        unpin: payload?.pinned === false || payload?.unpin === true
      })),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Закрепление сообщения Telegram'
    );
    saveTelegramClientSession(client);
    return { ok: true, pinned: payload?.pinned !== false };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_PIN_ERROR');
  }
}

async function editTelegramMessage(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const messageId = normalizeTelegramReplyToId(payload?.messageId || '');
    const text = cleanTelegramMultiline(payload?.text || payload?.message || '', 6000);
    if (!peerId || !messageId || !text) {
      throw Object.assign(new Error('Не удалось изменить Telegram-сообщение.'), {
        code: 'TELEGRAM_EDIT_INVALID'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const message = await withTelegramTimeout(
      client.editMessage(entity, {
        message: messageId,
        text,
        linkPreview: true
      }),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Редактирование сообщения Telegram'
    );
    saveTelegramClientSession(client);
    return {
      ok: true,
      message: normalizeTelegramMessage(message, chatId, settings)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_EDIT_ERROR');
  }
}

async function toggleTelegramMessageReaction(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_REACTION_UNSUPPORTED',
        error: 'Реакции через Telegram Web bridge недоступны.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const messageId = normalizeTelegramReplyToId(payload?.messageId || payload?.msgId || payload?.id || '');
    const emoji = getTelegramReactionDisplayEmoji(payload?.reaction || payload?.emoji || '');
    const hasExplicitAddRemove = (
      Object.prototype.hasOwnProperty.call(payload || {}, 'add')
      || Object.prototype.hasOwnProperty.call(payload || {}, 'remove')
    );
    const shouldSet = hasExplicitAddRemove
      ? (payload?.add !== false && payload?.remove !== true)
      : payload?.selected !== true;
    if (!peerId || !messageId || (shouldSet && !emoji)) {
      throw Object.assign(new Error('Не удалось определить Telegram-сообщение или реакцию.'), {
        code: 'TELEGRAM_REACTION_INVALID'
      });
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const reaction = shouldSet
      ? [new dependency.Api.ReactionEmoji({ emoticon: emoji })]
      : [];
    await withTelegramTimeout(
      client.invoke(new dependency.Api.messages.SendReaction({
        peer: entity,
        msgId: messageId,
        reaction,
        addToRecent: shouldSet || undefined
      })),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Отправка реакции Telegram'
    );

    let refreshedMessage = null;
    try {
      const refreshed = await withTelegramTimeout(
        client.getMessages(entity, { ids: messageId }),
        TELEGRAM_MESSAGES_TIMEOUT_MS,
        'Обновление реакции Telegram'
      );
      refreshedMessage = Array.isArray(refreshed) ? refreshed[0] : refreshed?.[0] || refreshed || null;
    } catch {
      refreshedMessage = null;
    }

    saveTelegramClientSession(client);
    return {
      ok: true,
      authorized: true,
      selected: shouldSet,
      emoji: shouldSet ? emoji : '',
      message: normalizeTelegramMessage(refreshedMessage, chatId, settings)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_REACTION_ERROR');
  }
}

async function deleteTelegramMessages(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_DELETE_UNSUPPORTED',
        error: 'Удаление сообщений через Telegram Web bridge недоступно.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const messageIds = Array.from(new Set(
      (Array.isArray(payload?.messageIds) ? payload.messageIds : [payload?.messageId])
        .map((value) => normalizeTelegramReplyToId(value))
        .filter(Boolean)
    ));
    if (!peerId || !messageIds.length) {
      throw Object.assign(new Error('Не удалось определить Telegram-сообщения для удаления.'), {
        code: 'TELEGRAM_DELETE_INVALID'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const deleteWithRevoke = (revoke) => withTelegramTimeout(
      client.deleteMessages(entity, messageIds, { revoke }),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Удаление сообщений Telegram'
    );
    try {
      await deleteWithRevoke(true);
    } catch (error) {
      await deleteWithRevoke(false);
    }
    saveTelegramClientSession(client);
    return {
      ok: true,
      deletedIds: messageIds.map((value) => String(value || '').trim()).filter(Boolean)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_DELETE_ERROR');
  }
}

function bufferFromIpcBytes(value = null) {
  if (Buffer.isBuffer(value)) return value;
  if (value instanceof ArrayBuffer) return Buffer.from(value);
  if (ArrayBuffer.isView(value)) return Buffer.from(value.buffer, value.byteOffset, value.byteLength);
  if (Array.isArray(value)) return Buffer.from(value);
  if (typeof value === 'string' && value.trim()) return Buffer.from(value.trim(), 'base64');
  return Buffer.alloc(0);
}

function normalizeWebSendFilesPayload(payload = {}) {
  const sourceFiles = Array.isArray(payload?.files)
    ? payload.files
    : (Array.isArray(payload?.attachments) ? payload.attachments : []);
  const seen = new Set();
  return sourceFiles
    .map((file, index) => {
      if (!file || typeof file !== 'object') return null;
      let base64 = '';
      let mimeType = cleanTelegramText(file?.mimeType || file?.type || file?.contentType || '', 180);
      const dataUrl = String(file?.dataUrl || file?.url || '').trim();
      if (/^data:/i.test(dataUrl)) {
        const match = dataUrl.match(/^data:([^;,]+)?(?:;[^,]*)?;base64,(.+)$/i);
        if (match) {
          mimeType = cleanTelegramText(mimeType || match[1] || '', 180);
          base64 = String(match[2] || '').trim();
        }
      }
      if (!base64) {
        const buffer = bufferFromIpcBytes(file?.bytes || file?.buffer || file?.base64 || null);
        if (buffer.length) {
          base64 = buffer.toString('base64');
        }
      }
      if (!base64) return null;
      const name = sanitizeOpenFileName(
        file?.name || file?.fileName || `file-${index + 1}.bin`,
        `file-${index + 1}.bin`
      );
      const normalizedMimeType = cleanTelegramText(mimeType || '', 180) || 'application/octet-stream';
      const size = Math.max(0, Number(file?.size || 0) || 0);
      const key = `${name}\u0001${normalizedMimeType}\u0001${size || base64.length}`;
      if (seen.has(key)) return null;
      seen.add(key);
      return {
        name,
        fileName: name,
        mimeType: normalizedMimeType,
        size,
        base64
      };
    })
    .filter(Boolean)
    .slice(0, 10);
}

async function sendTelegramFiles(payload = {}) {
  try {
    const dependency = getTelegramDependency();
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      await selectTelegramWebDialog(payload, {
        showWindow: true,
        focusWindow: true,
        waitAfterSelectMs: 250
      }).catch(() => null);
      return {
        ok: false,
        code: 'TELEGRAM_WEB_FILES_UNSUPPORTED',
        error: 'Файлы через Telegram Web bridge пока отправляются только из окна Telegram Web. Откройте Web-окно для этого диалога.'
      };
    }
    if (!dependency.ok) {
      throw Object.assign(new Error(`GramJS недоступен: ${dependency.error}`), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    const files = (Array.isArray(payload?.files) ? payload.files : [])
      .map((file, index) => {
        const buffer = bufferFromIpcBytes(file?.bytes || file?.buffer || file?.base64 || null);
        const name = sanitizeOpenFileName(file?.name || file?.fileName || `telegram-file-${index + 1}.bin`, `telegram-file-${index + 1}.bin`);
        return buffer.length ? new dependency.CustomFile(name, Number(file?.size || buffer.length) || buffer.length, '', buffer) : null;
      })
      .filter(Boolean);
    const caption = cleanTelegramMultiline(payload?.text || payload?.caption || '', 6000);
    if (!peerId || !files.length) {
      throw Object.assign(new Error('Не удалось подготовить файлы для Telegram.'), {
        code: 'TELEGRAM_FILES_EMPTY'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const replyTo = normalizeTelegramReplyToId(payload?.inReplyToMessageId || payload?.replyToMessageId || '');
    const response = await withTelegramTimeout(
      client.sendFile(entity, {
        file: files.length === 1 ? files[0] : files,
        caption,
        replyTo: replyTo || undefined,
        supportsStreaming: true,
        scheduleDate: normalizeTelegramScheduleDate(payload?.scheduledAt || payload?.scheduleDate || 0) || undefined,
        workers: 2
      }),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Отправка файлов Telegram'
    );
    const rawMessages = Array.isArray(response) ? response : [response].filter(Boolean);
    saveTelegramClientSession(client);
    return {
      ok: true,
      messages: normalizeTelegramMessageList(rawMessages, chatId, settings),
      message: normalizeTelegramMessage(rawMessages[rawMessages.length - 1] || null, chatId, settings)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_FILES_SEND_ERROR');
  }
}

async function forwardTelegramMessages(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const sourceChatId = normalizeTelegramChatId(payload?.sourceChatId || payload?.fromChatId || '');
    const targetChatId = normalizeTelegramChatId(payload?.targetChatId || payload?.chatId || payload?.toChatId || '');
    if (isTelegramWebChatId(sourceChatId) || isTelegramWebChatId(targetChatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_FORWARD_UNSUPPORTED',
        error: 'Нативная пересылка через Telegram Web bridge недоступна. YuChat отправит текст как обычное сообщение.'
      };
    }
    const sourcePeerId = cleanTelegramText(payload?.sourcePeerId || getTelegramPeerIdFromChatId(sourceChatId), 220);
    const targetPeerId = cleanTelegramText(payload?.targetPeerId || getTelegramPeerIdFromChatId(targetChatId), 220);
    const messageIds = Array.from(new Set((Array.isArray(payload?.messageIds) ? payload.messageIds : [])
      .map((value) => normalizeTelegramReplyToId(value))
      .filter(Boolean)));
    if (!sourcePeerId || !targetPeerId || !messageIds.length) {
      throw Object.assign(new Error('Не удалось определить Telegram-сообщения для пересылки.'), {
        code: 'TELEGRAM_FORWARD_INVALID'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const sourceEntity = await resolveTelegramEntity(client, sourceChatId, sourcePeerId);
    const targetEntity = await resolveTelegramEntity(client, targetChatId, targetPeerId);
    const response = await withTelegramTimeout(
      client.forwardMessages(targetEntity, {
        messages: messageIds,
        fromPeer: sourceEntity
      }),
      TELEGRAM_SEND_TIMEOUT_MS,
      'Пересылка сообщений Telegram'
    );
    const rawMessages = Array.isArray(response) ? response : [response].filter(Boolean);
    saveTelegramClientSession(client);
    return {
      ok: true,
      messages: normalizeTelegramMessageList(rawMessages, targetChatId, settings)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_FORWARD_ERROR');
  }
}

async function markTelegramChatAsRead(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return await markTelegramWebChatAsRead(payload);
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) return { ok: false, error: 'Не удалось определить Telegram-диалог.' };
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const maxId = normalizeTelegramReplyToId(payload?.untilMessageId || payload?.messageId || '');
    await withTelegramTimeout(
      maxId ? client.markAsRead(entity, undefined, { maxId }) : client.markAsRead(entity),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Отметка Telegram как прочитанного'
    );
    saveTelegramClientSession(client);
    return { ok: true };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_MARK_READ_ERROR');
  }
}

async function updateTelegramArchiveState(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_ARCHIVE_UNSUPPORTED',
        error: 'Архив Telegram Web bridge меняется только через Telegram API.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) return { ok: false, error: 'Не удалось определить Telegram-диалог.' };
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const inputPeer = typeof client.getInputEntity === 'function'
      ? await client.getInputEntity(entity)
      : entity;
    const archived = payload?.archived === true;
    const folderId = archived ? 1 : 0;
    await withTelegramTimeout(
      client.invoke(new dependency.Api.folders.EditPeerFolders({
        folderPeers: [
          new dependency.Api.InputFolderPeer({
            peer: inputPeer,
            folderId
          })
        ]
      })),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Обновление архива Telegram'
    );
    saveTelegramClientSession(client);
    return {
      ok: true,
      archived,
      folderId
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_ARCHIVE_UPDATE_ERROR');
  }
}

async function updateTelegramDialogPinnedState(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_PIN_DIALOG_UNSUPPORTED',
        error: 'Закрепление Telegram Web bridge меняется только через Telegram API.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) return { ok: false, error: 'Не удалось определить Telegram-диалог.' };
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const inputPeer = typeof client.getInputEntity === 'function'
      ? await client.getInputEntity(entity)
      : entity;
    const pinned = payload?.pinned !== false && payload?.pin !== false && payload?.unpin !== true;
    await withTelegramTimeout(
      client.invoke(new dependency.Api.messages.ToggleDialogPin({
        pinned,
        peer: new dependency.Api.InputDialogPeer({
          peer: inputPeer
        })
      })),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      pinned ? 'Закрепление Telegram-диалога' : 'Открепление Telegram-диалога'
    );
    saveTelegramClientSession(client);
    return {
      ok: true,
      pinned,
      pinnedAt: pinned ? TELEGRAM_DIALOG_PINNED_AT : ''
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_DIALOG_PIN_UPDATE_ERROR');
  }
}

async function leaveTelegramDialog(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_LEAVE_UNSUPPORTED',
        error: 'Покинуть Telegram Web bridge можно только в окне Telegram.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) {
      return {
        ok: false,
        code: 'TELEGRAM_PEER_MISSING',
        error: 'Не удалось определить Telegram-диалог.'
      };
    }
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка авторизации Telegram'
    ).catch(() => false);
    if (!authorized) {
      return {
        ok: false,
        code: 'TELEGRAM_AUTH_REQUIRED',
        error: 'Telegram не авторизован. Выполните вход в настройках.',
        authorized: false
      };
    }
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    if (typeof client.kickParticipant === 'function') {
      await withTelegramTimeout(
        client.kickParticipant(entity, 'me'),
        TELEGRAM_SEND_TIMEOUT_MS,
        'Выход из Telegram-канала'
      );
    } else {
      const inputPeer = typeof client.getInputEntity === 'function'
        ? await client.getInputEntity(entity)
        : entity;
      await withTelegramTimeout(
        client.invoke(new dependency.Api.channels.LeaveChannel({
          channel: inputPeer
        })),
        TELEGRAM_SEND_TIMEOUT_MS,
        'Выход из Telegram-канала'
      );
    }
    saveTelegramClientSession(client);
    return {
      ok: true,
      left: true,
      chatId,
      resolvedWorkspaceId: 'telegram'
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_LEAVE_DIALOG_ERROR');
  }
}

async function updateTelegramNotifySettings(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_NOTIFY_UNSUPPORTED',
        error: 'Настройки уведомлений Telegram Web bridge меняются только в Telegram.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (!peerId) return { ok: false, error: 'Не удалось определить Telegram-диалог.' };
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const inputPeer = typeof client.getInputEntity === 'function'
      ? await client.getInputEntity(entity)
      : entity;
    const muted = payload?.muted === true || payload?.isMuted === true;
    const muteUntil = muted ? 2147483647 : 0;
    await withTelegramTimeout(
      client.invoke(new dependency.Api.account.UpdateNotifySettings({
        peer: new dependency.Api.InputNotifyPeer({
          peer: inputPeer
        }),
        settings: new dependency.Api.InputPeerNotifySettings({
          muteUntil
        })
      })),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Настройки уведомлений Telegram'
    );
    saveTelegramClientSession(client);
    return {
      ok: true,
      notifySettings: {
        isMuted: muted,
        muteUntil,
        rule: muted ? 'MUTED' : 'DEFAULT'
      },
      isMuted: muted
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_NOTIFY_UPDATE_ERROR');
  }
}

async function startTelegramDirectCall(payload = {}) {
  try {
    const settings = normalizeTelegramApiSettings(payload?.settings || payload);
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    if (isTelegramWebChatId(chatId)) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_CALL_UNSUPPORTED',
        error: 'Звонок через Telegram Web bridge недоступен.'
      };
    }
    const peerId = cleanTelegramText(payload?.peerId || getTelegramPeerIdFromChatId(chatId), 220);
    if (TELEGRAM_CALL_MEDIA_ENGINE_AVAILABLE !== true) {
      return {
        ok: false,
        code: 'TELEGRAM_CALL_MEDIA_ENGINE_MISSING',
        error: 'Звонки Telegram пока недоступны в этой сборке.'
      };
    }
    if (!peerId) return { ok: false, error: 'Не удалось определить Telegram-диалог.' };
    const dependency = getTelegramDependency();
    if (!dependency.ok) {
      throw Object.assign(new Error(dependency.error || 'Модуль Telegram недоступен.'), {
        code: 'TELEGRAM_DEPENDENCY_MISSING'
      });
    }
    const { client } = await ensureTelegramClient(settings);
    const entity = await resolveTelegramEntity(client, chatId, peerId);
    const inputUser = typeof client.getInputEntity === 'function'
      ? await client.getInputEntity(entity)
      : entity;
    const requestUser = typeof dependency.Utils?.getInputUser === 'function'
      ? dependency.Utils.getInputUser(inputUser)
      : inputUser;
    const randomId = crypto.randomBytes(4).readInt32LE(0);
    const handshake = await buildTelegramOutgoingCallHandshake(client, dependency.Api);
    const result = await withTelegramTimeout(
      client.invoke(new dependency.Api.phone.RequestCall({
        userId: requestUser,
        randomId,
        gAHash: handshake.gAHash,
        video: payload?.video === true,
        protocol: buildTelegramPhoneCallProtocol(dependency.Api)
      })),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Запуск звонка Telegram'
    );
    rememberTelegramOutgoingCallState(result?.phoneCall || result?.call || result, handshake, settings);
    saveTelegramClientSession(client);
    return {
      ok: true,
      callId: normalizeTelegramPeerId(result?.phoneCall?.id || result?.call?.id || result?.id || ''),
      status: cleanTelegramText(result?.phoneCall?.className || result?.call?.className || result?.className || 'requested', 120)
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_CALL_ERROR');
  }
}

function buildTelegramMediaCacheFilePath(fileName = 'telegram-file.bin') {
  const tempDir = path.join(app.getPath('temp'), YUCHAT_STORAGE_PROFILE_NAME, 'telegram-media');
  ensureDirSync(tempDir);
  const safeName = sanitizeOpenFileName(fileName, 'telegram-file.bin');
  const extension = path.extname(safeName);
  const baseName = path.basename(safeName, extension).slice(0, 120) || 'telegram-file';
  return path.join(tempDir, `${baseName}-${Date.now()}-${Math.random().toString(36).slice(2, 8)}${extension}`);
}

async function downloadTelegramMediaRecord(record = null) {
  if (!record || typeof record !== 'object') {
    throw Object.assign(new Error('Telegram-медиа не найдено.'), {
      code: 'TELEGRAM_MEDIA_NOT_FOUND'
    });
  }
  if (record.filePath && fs.existsSync(record.filePath)) {
    return record.filePath;
  }
  const { client } = await ensureTelegramClient(record.settings || {});
  const isProfilePhoto = record.kind === 'profile-photo';
  const body = isProfilePhoto
    ? await downloadTelegramProfilePhoto(client, record, TELEGRAM_MEDIA_DOWNLOAD_TIMEOUT_MS)
    : await (async () => {
      const candidates = [
        record.message,
        record.media,
        record.media?.photo,
        record.media?.document
      ].filter(Boolean);
      let lastError = null;
      for (const candidate of candidates) {
        try {
          const downloaded = await withTelegramTimeout(
            client.downloadMedia(candidate, {
              workers: 2
            }),
            TELEGRAM_MEDIA_DOWNLOAD_TIMEOUT_MS,
            'Загрузка Telegram-медиа'
          );
          const buffer = bufferFromTelegramDownloadResult(downloaded);
          if (buffer.length > 0) return buffer;
        } catch (error) {
          lastError = error;
        }
      }
      if (lastError) throw lastError;
      return Buffer.alloc(0);
    })();
  if (!body.length) {
    throw Object.assign(new Error('Telegram не вернул файл.'), {
      code: 'TELEGRAM_MEDIA_EMPTY'
    });
  }
  const filePath = buildTelegramMediaCacheFilePath(record.fileName || 'telegram-file.bin');
  fs.writeFileSync(filePath, body);
  record.filePath = filePath;
  record.size = body.length;
  saveTelegramClientSession(client);
  return filePath;
}

async function logoutTelegramIntegration() {
  try {
    telegramWebDialogCache = [];
    telegramWebDialogCacheUpdatedAt = 0;
    const dependency = getTelegramDependency();
    if (telegramClient && dependency.ok) {
      try {
        await withTelegramTimeout(
          telegramClient.invoke(new dependency.Api.auth.LogOut()),
          TELEGRAM_CONNECT_TIMEOUT_MS,
          'Выход из Telegram'
        );
      } catch {
        // Session may already be invalid; local cleanup is still correct.
      }
    }
    await disconnectTelegramClient();
    setStoredTelegramSessionString('');
    return { ok: true };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_LOGOUT_ERROR');
  }
}

const TELEGRAM_WEB_DIALOG_SCRAPE_SCRIPT = `(() => {
  const clean = (value, limit = 260) => String(value || '').replace(/\\s+/g, ' ').trim().slice(0, limit);
  const pickText = (root, selectors, limit = 260) => {
    for (const selector of selectors) {
      const node = root.querySelector(selector);
      const text = clean(node && (node.innerText || node.textContent), limit);
      if (text) return text;
    }
    return '';
  };
  const parseUnread = (root) => {
    const nodes = Array.from(root.querySelectorAll('[class*="badge"], [class*="Badge"], [class*="unread"], [class*="Unread"]'));
    for (const node of nodes) {
      const text = clean(node.textContent, 16);
      const match = text.match(/\\d+/);
      if (match) return Math.max(0, Math.min(9999, Number(match[0]) || 0));
    }
    return 0;
  };
  const selectors = [
    'a.chat-item-clickable',
    'a.ListItem',
    '.chat-item-clickable',
    '.ChatList a',
    '.chat-list a',
    '[data-peer-id]',
    '[data-testid*="chat"]',
    '[role="listitem"]'
  ];
  const nodes = new Set();
  for (const selector of selectors) {
    try {
      document.querySelectorAll(selector).forEach((node) => nodes.add(node));
    } catch {}
  }
  if (!nodes.size) {
    document.querySelectorAll('a[href^="#"]').forEach((node) => nodes.add(node));
  }
  const seen = new Set();
  const dialogs = [];
  for (const node of nodes) {
    if (!(node instanceof HTMLElement)) continue;
    const rect = node.getBoundingClientRect();
    if (rect.width < 120 || rect.height < 28) continue;
    const rawText = String(node.innerText || node.textContent || '').trim();
    if (!rawText) continue;
    const lines = rawText.split('\\n').map((line) => clean(line, 220)).filter(Boolean);
    let title = pickText(node, [
      '.title',
      '.Title',
      '.chat-title',
      '.peer-title',
      '.fullName',
      '.name',
      '.ChatInfo .title',
      'h3',
      '[dir="auto"]'
    ], 180) || lines[0] || '';
    title = clean(title, 180);
    if (!title || /^(telegram web|log in|sign in|phone number|settings|menu)$/i.test(title)) continue;
    const href = clean(node.getAttribute('href') || '', 260);
    const dataPeerId = clean(node.getAttribute('data-peer-id') || node.dataset.peerId || node.dataset.dialogId || '', 120);
    const key = dataPeerId || href || title;
    if (!key || seen.has(key)) continue;
    seen.add(key);
    const preview = pickText(node, [
      '.subtitle',
      '.Subtitle',
      '.last-message',
      '.lastMessage',
      '.message',
      '.status',
      '.description'
    ], 260) || lines.slice(1).filter((line) => line !== title).join(' ');
    const usernameMatch = href.match(/@([A-Za-z0-9_]{3,})/);
    const type = /(^#|channel|канал)/i.test(rawText) ? 'channel' : /group|группа|members|участник/i.test(rawText) ? 'group' : 'user';
    dialogs.push({
      id: key,
      title,
      username: usernameMatch ? usernameMatch[1] : '',
      type,
      unreadCount: parseUnread(node),
      previewText: clean(preview, 320),
      href
    });
    if (dialogs.length >= 160) break;
  }
  const bodyText = clean(document.body && document.body.innerText, 1000);
  const loginVisible = /phone number|log in|sign in|код|номер телефона/i.test(bodyText) && dialogs.length < 3;
  return {
    ok: true,
    href: location.href,
    title: document.title || '',
    loginVisible,
    authorized: dialogs.length > 0 && !loginVisible,
    dialogs,
    capturedAt: Date.now()
  };
})()`;

function normalizeTelegramWebDialog(rawDialog = null, index = 0) {
  if (!isPlainRecord(rawDialog)) return null;
  const title = cleanTelegramText(rawDialog.title || '', 180);
  if (!title) return null;
  const rawId = cleanTelegramText(rawDialog.id || rawDialog.href || title, 240);
  const id = rawId || `${title}:${index}`;
  const type = ['channel', 'group', 'user'].includes(cleanTelegramText(rawDialog.type || '', 20))
    ? cleanTelegramText(rawDialog.type || '', 20)
    : 'user';
  const timestamp = Date.now() - index;
  return {
    id,
    chatId: `tg:web:${id}`,
    title,
    type,
    username: cleanTelegramText(rawDialog.username || '', 120),
    unreadCount: Math.max(0, Math.trunc(Number(rawDialog.unreadCount || 0) || 0)),
    unreadMentionsCount: 0,
    previewText: cleanTelegramText(rawDialog.previewText || 'Диалог Telegram Web', 320),
    previewTimestamp: timestamp,
    updatedAt: timestamp,
    webHref: cleanTelegramText(rawDialog.href || '', 260),
    sourceMode: 'web'
  };
}

function isTelegramWebChatId(value = '') {
  return false;
}

function getTelegramWebDialogIdFromChatId(chatId = '') {
  return '';
}

function getTelegramWebDialogByChatId(chatId = '') {
  const id = getTelegramWebDialogIdFromChatId(chatId);
  if (!id) return null;
  return (Array.isArray(telegramWebDialogCache) ? telegramWebDialogCache : []).find((dialog) => (
    cleanTelegramText(dialog?.id || '', 260) === id
    || cleanTelegramText(dialog?.chatId || '', 320) === normalizeTelegramChatId(chatId)
  )) || null;
}

function buildTelegramWebExecutorScript(fn, payload = {}) {
  return `(${fn.toString()})(${JSON.stringify(payload || {})})`;
}

const TELEGRAM_WEB_SELECT_DIALOG_EXECUTOR = function selectTelegramWebDialogInPage(payload) {
  const clean = (value, limit = 260) => String(value || '').replace(/\s+/g, ' ').trim().slice(0, limit);
  const wantedId = clean(payload.id || '', 260);
  const wantedTitle = clean(payload.title || '', 180).toLowerCase();
  const wantedHref = clean(payload.href || '', 260);
  const selectors = [
    'a.chat-item-clickable',
    'a.ListItem',
    '.chat-item-clickable',
    '.ChatList a',
    '.chat-list a',
    '[data-peer-id]',
    '[data-testid*="chat"]',
    '[role="listitem"]',
    'a[href^="#"]'
  ];
  const nodes = [];
  selectors.forEach((selector) => {
    try {
      document.querySelectorAll(selector).forEach((node) => {
        if (node instanceof HTMLElement && !nodes.includes(node)) nodes.push(node);
      });
    } catch {}
  });
  const scoreNode = (node) => {
    const text = clean(node.innerText || node.textContent || '', 420);
    const title = clean(
      node.querySelector('.title,.Title,.chat-title,.peer-title,.fullName,.name,[dir="auto"]')?.textContent
      || text.split('\n')[0]
      || '',
      180
    );
    const href = clean(node.getAttribute('href') || '', 260);
    const peerId = clean(node.getAttribute('data-peer-id') || node.dataset.peerId || node.dataset.dialogId || '', 160);
    let score = 0;
    if (wantedHref && href === wantedHref) score += 100;
    if (wantedId && (peerId === wantedId || href === wantedId)) score += 90;
    if (wantedTitle && title.toLowerCase() === wantedTitle) score += 70;
    if (wantedTitle && text.toLowerCase().includes(wantedTitle)) score += 25;
    return { score, title, href, peerId };
  };
  let best = null;
  nodes.forEach((node) => {
    const rect = node.getBoundingClientRect();
    if (rect.width < 80 || rect.height < 20) return;
    const scored = scoreNode(node);
    if (scored.score <= 0) return;
    if (!best || scored.score > best.score) best = { node, ...scored };
  });
  if (best?.node) {
    best.node.scrollIntoView({ block: 'center', inline: 'nearest' });
    best.node.click();
    return { ok: true, clicked: true, title: best.title, href: best.href, peerId: best.peerId };
  }
  if (wantedHref && wantedHref.startsWith('#')) {
    location.hash = wantedHref;
    return { ok: true, navigated: true, href: wantedHref };
  }
  return { ok: false, error: 'Диалог не найден в Telegram Web.' };
};

const TELEGRAM_WEB_MESSAGES_EXECUTOR = function scrapeTelegramWebMessagesInPage(payload) {
  const clean = (value, limit = 6000) => String(value || '').replace(/\u00a0/g, ' ').replace(/[ \t]+/g, ' ').trim().slice(0, limit);
  const hash = (value) => {
    let result = 0;
    const source = String(value || '');
    for (let index = 0; index < source.length; index += 1) {
      result = ((result << 5) - result + source.charCodeAt(index)) | 0;
    }
    return Math.abs(result).toString(36);
  };
  const selectors = [
    '[data-message-id]',
    '.Message',
    '.message',
    '.message-list-item',
    '.ServiceMessage',
    '.service-message',
    '[class*="ServiceMessage"]',
    '[class*="Message"][class*="message"]',
    '[id^="message"]'
  ];
  const nodes = [];
  selectors.forEach((selector) => {
    try {
      document.querySelectorAll(selector).forEach((node) => {
        if (node instanceof HTMLElement && !nodes.includes(node)) nodes.push(node);
      });
    } catch {}
  });
  const timePattern = /^(?:[01]?\d|2[0-3]):[0-5]\d(?:\s*(?:AM|PM))?$/i;
  const items = [];
  nodes.forEach((node, index) => {
    const rect = node.getBoundingClientRect();
    if (rect.width < 80 || rect.height < 12) return;
    const rawText = clean(node.innerText || node.textContent || '', 6000);
    const className = String(node.className || '');
    const hasMedia = Boolean(node.querySelector('img,video,audio,[class*="media"],[class*="Media"],[class*="document"],[class*="Document"]'));
    const looksLikeCallService = /(?:call|phone|voice|video-call|звон)/i.test(`${rawText} ${className}`)
      || Boolean(node.querySelector('[class*="call"],[class*="Call"],[class*="phone"],[class*="Phone"]'));
    if (!rawText && !hasMedia) return;
    const rawLines = rawText.split(/\n+/).map((line) => clean(line, 500)).filter(Boolean);
    const author = clean(
      node.querySelector('.sender-title,.Sender,.sender,.message-title,.message-author,.peer-title')?.textContent
      || '',
      160
    );
    const lines = rawLines.filter((line) => {
      if (!line) return false;
      if (author && line === author) return false;
      if (timePattern.test(line)) return false;
      if (/^(edited|изменено|seen|просмотрено)$/i.test(line)) return false;
      return true;
    });
    const text = clean(lines.join('\n'), 6000);
    const dataId = clean(
      node.getAttribute('data-message-id')
      || node.dataset.messageId
      || node.dataset.mid
      || node.id
      || '',
      120
    );
    const isMine = /\b(own|out|outgoing|is-out|message-out)\b/i.test(className)
      || Boolean(node.closest('.own,.outgoing,.message-out,.is-out'));
    if (!text && !hasMedia && !looksLikeCallService) return;
    const callText = looksLikeCallService
      ? clean(text || rawText || (isMine ? 'Исходящий звонок' : 'Входящий звонок'), 6000)
      : '';
    items.push({
      id: dataId || `web-${hash(`${rawText}:${index}`)}`,
      text: callText || text || (hasMedia ? 'Вложение Telegram Web' : ''),
      authorName: author || (isMine ? 'Вы' : 'Telegram'),
      isMine,
      timestamp: Date.now() - Math.max(0, nodes.length - index) * 1000,
      hasMedia,
      isSystem: looksLikeCallService,
      serviceKind: looksLikeCallService ? 'telegram_call' : '',
      attachmentLabel: looksLikeCallService ? 'Звонок' : ''
    });
  });
  const limit = Math.max(1, Math.min(200, Number(payload.limit || payload.count || 80) || 80));
  return {
    ok: true,
    href: location.href,
    title: document.title || '',
    items: items.slice(-limit)
  };
};

const TELEGRAM_WEB_SEND_TEXT_EXECUTOR = async function sendTelegramWebTextInPage(payload) {
  const text = String(payload.text || '');
  const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
  if (!text.trim()) return { ok: false, error: 'Пустое сообщение.' };
  const editorSelectors = [
    '#editable-message-text',
    '[contenteditable="true"][role="textbox"]',
    '[contenteditable="true"]',
    '[role="textbox"]',
    '.input-message-input',
    '.composer_rich_textarea'
  ];
  let editor = null;
  for (const selector of editorSelectors) {
    editor = document.querySelector(selector);
    if (editor instanceof HTMLElement) break;
    editor = null;
  }
  if (!editor) return { ok: false, error: 'Поле ввода Telegram Web не найдено.' };
  editor.focus();
  try {
    document.execCommand('selectAll', false, null);
    document.execCommand('insertText', false, text);
  } catch {
    editor.textContent = text;
  }
  editor.dispatchEvent(new InputEvent('input', {
    bubbles: true,
    inputType: 'insertText',
    data: text
  }));
  await sleep(80);
  const sendButton = Array.from(document.querySelectorAll('button,[role="button"]')).find((node) => {
    const label = `${node.getAttribute('aria-label') || ''} ${node.title || ''} ${node.textContent || ''}`;
    return /send|отправ|paper|plane/i.test(label) || /send|Send/.test(String(node.className || ''));
  });
  if (sendButton instanceof HTMLElement) {
    sendButton.click();
    return { ok: true, sent: true };
  }
  const enterEvent = new KeyboardEvent('keydown', {
    key: 'Enter',
    code: 'Enter',
    keyCode: 13,
    which: 13,
    bubbles: true,
    cancelable: true
  });
  editor.dispatchEvent(enterEvent);
  return { ok: true, sent: true, viaEnter: true };
};

const TELEGRAM_WEB_AUTH_SNAPSHOT_SCRIPT = `(() => {
  const readStorage = (storage) => {
    const output = {};
    if (!storage) return output;
    for (let index = 0; index < storage.length; index += 1) {
      const key = storage.key(index);
      if (!key || !/(^dc\\d+_|auth|user|salt|session)/i.test(key)) continue;
      try {
        output[key] = storage.getItem(key);
      } catch {}
    }
    return output;
  };
  return {
    ok: true,
    href: location.href,
    title: document.title || '',
    localStorage: readStorage(window.localStorage),
    sessionStorage: readStorage(window.sessionStorage),
    capturedAt: Date.now()
  };
})()`;

function parseTelegramWebStorageValue(value = null, depth = 0) {
  if (depth > 5) return value;
  if (typeof value !== 'string') return value;
  const trimmed = value.trim();
  if (!trimmed) return '';
  if (
    (trimmed.startsWith('"') && trimmed.endsWith('"'))
    || (trimmed.startsWith('{') && trimmed.endsWith('}'))
    || (trimmed.startsWith('[') && trimmed.endsWith(']'))
  ) {
    try {
      return parseTelegramWebStorageValue(JSON.parse(trimmed), depth + 1);
    } catch {
      return trimmed;
    }
  }
  return trimmed.replace(/^['"]+|['"]+$/g, '').trim();
}

function normalizeTelegramWebByteBuffer(candidate = null) {
  const parsed = parseTelegramWebStorageValue(candidate);
  if (Buffer.isBuffer(parsed)) return parsed;
  if (parsed instanceof ArrayBuffer) return Buffer.from(parsed);
  if (ArrayBuffer.isView(parsed)) return Buffer.from(parsed.buffer, parsed.byteOffset, parsed.byteLength);
  if (Array.isArray(parsed)) {
    const values = parsed.map((value) => Number(value));
    if (values.length && values.every((value) => Number.isInteger(value) && value >= 0 && value <= 255)) {
      return Buffer.from(values);
    }
  }
  if (isPlainRecord(parsed)) {
    const directCandidates = [
      parsed.data,
      parsed.bytes,
      parsed.buffer,
      parsed.key,
      parsed.authKey,
      parsed.auth_key,
      parsed.value
    ];
    for (const directCandidate of directCandidates) {
      const buffer = normalizeTelegramWebByteBuffer(directCandidate);
      if (buffer.length) return buffer;
    }
  }
  if (typeof parsed === 'string') {
    const compact = parsed.replace(/\s+/g, '');
    if (/^[0-9a-f]+$/iu.test(compact) && compact.length % 2 === 0) {
      return Buffer.from(compact, 'hex');
    }
    if (/^[A-Za-z0-9+/_=-]+$/u.test(compact) && compact.length >= 300) {
      try {
        return Buffer.from(compact.replace(/-/g, '+').replace(/_/g, '/'), 'base64');
      } catch {
        return Buffer.alloc(0);
      }
    }
    if (/^\d+(?:,\d+)+$/u.test(compact)) {
      const values = compact.split(',').map((value) => Number(value));
      if (values.every((value) => Number.isInteger(value) && value >= 0 && value <= 255)) {
        return Buffer.from(values);
      }
    }
  }
  return Buffer.alloc(0);
}

function getTelegramWebAuthKeyFromValue(value = null) {
  const buffer = normalizeTelegramWebByteBuffer(value);
  if (buffer.length === 256) return buffer;
  if (buffer.length > 256) {
    const first = buffer.subarray(0, 256);
    const last = buffer.subarray(buffer.length - 256);
    if (first.some((byte) => byte !== 0)) return first;
    if (last.some((byte) => byte !== 0)) return last;
  }
  return Buffer.alloc(0);
}

function findTelegramWebUserDcId(snapshot = null) {
  const areas = [
    snapshot?.localStorage,
    snapshot?.sessionStorage
  ].filter((area) => area && typeof area === 'object');
  const dcCandidates = [];
  const visit = (value = null, depth = 0) => {
    const parsed = parseTelegramWebStorageValue(value);
    if (depth > 5 || parsed == null) return;
    if (typeof parsed === 'number' || typeof parsed === 'string') {
      const numeric = Math.trunc(Number(parsed));
      if (numeric >= 1 && numeric <= 5) dcCandidates.push(numeric);
      return;
    }
    if (Array.isArray(parsed)) {
      parsed.forEach((item) => visit(item, depth + 1));
      return;
    }
    if (isPlainRecord(parsed)) {
      Object.entries(parsed).forEach(([key, item]) => {
        if (/^(dc|dcid|dc_id|dcID|mainDcId|main_dc_id)$/iu.test(String(key || ''))) {
          visit(item, depth + 1);
        } else if (/auth|user|session/iu.test(String(key || ''))) {
          visit(item, depth + 1);
        }
      });
    }
  };
  areas.forEach((area) => {
    Object.entries(area).forEach(([key, value]) => {
      if (/user_auth|auth_user|session|state/iu.test(String(key || ''))) {
        visit(value, 0);
      }
    });
  });
  return dcCandidates.find((dcId) => dcId >= 1 && dcId <= 5) || 0;
}

function extractTelegramWebAuthKey(snapshot = null) {
  const areas = [
    snapshot?.localStorage,
    snapshot?.sessionStorage
  ].filter((area) => area && typeof area === 'object');
  const userDcId = findTelegramWebUserDcId(snapshot);
  const candidates = [];
  areas.forEach((area) => {
    Object.entries(area).forEach(([key, value]) => {
      const match = /^dc(\d+)_auth_key$/iu.exec(String(key || '').trim());
      if (!match) return;
      const dcId = Math.trunc(Number(match[1]) || 0);
      if (dcId < 1 || dcId > 5) return;
      const authKey = getTelegramWebAuthKeyFromValue(value);
      if (authKey.length === 256) {
        candidates.push({ dcId, authKey, preferred: userDcId === dcId });
      }
    });
  });
  return candidates.find((candidate) => candidate.preferred)
    || candidates[0]
    || null;
}

function buildGramjsStringSessionFromAuthKey(dcId = 0, authKey = null) {
  const normalizedDcId = Math.trunc(Number(dcId || 0) || 0);
  const key = Buffer.isBuffer(authKey) ? authKey : Buffer.alloc(0);
  if (normalizedDcId < 1 || normalizedDcId > 5 || key.length !== 256) return '';
  const address = TELEGRAM_DC_ADDRESS_BY_ID[normalizedDcId] || TELEGRAM_DC_ADDRESS_BY_ID[4];
  const addressBuffer = Buffer.from(address);
  const addressLengthBuffer = Buffer.alloc(2);
  addressLengthBuffer.writeInt16BE(addressBuffer.length, 0);
  const portBuffer = Buffer.alloc(2);
  portBuffer.writeInt16BE(80, 0);
  return `1${Buffer.concat([
    Buffer.from([normalizedDcId]),
    addressLengthBuffer,
    addressBuffer,
    portBuffer,
    key
  ]).toString('base64')}`;
}

async function importTelegramWebSession(payload = {}) {
  const settings = normalizeTelegramApiSettings(payload?.settings || payload);
  await openTelegramWebWindow({ settings }, {
    show: payload?.showWindow !== false,
    focus: payload?.focusWindow !== false,
    preserveCurrent: true
  });
  if (!telegramWebWindow || telegramWebWindow.isDestroyed()) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_NOT_OPEN',
      error: 'Откройте Telegram Web и войдите в аккаунт.'
    };
  }
  const snapshot = await telegramWebWindow.webContents.executeJavaScript(TELEGRAM_WEB_AUTH_SNAPSHOT_SCRIPT, true);
  const extracted = extractTelegramWebAuthKey(snapshot);
  if (!extracted?.authKey?.length) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_SESSION_NOT_FOUND',
      error: 'Не нашёл auth key в Telegram Web. Войдите в Web-окне и повторите импорт.'
    };
  }
  const sessionString = buildGramjsStringSessionFromAuthKey(extracted.dcId, extracted.authKey);
  if (!sessionString) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_SESSION_INVALID',
      error: 'Telegram Web-сессия найдена, но её не удалось подготовить для MTProto.'
    };
  }

  const previousSessionString = getStoredTelegramSessionString();
  await disconnectTelegramClient();
  setStoredTelegramSessionString(sessionString);
  try {
    const { client, proxyLabel, proxyMode, fakeTlsDomain } = await ensureTelegramClient(settings);
    const authorized = await withTelegramTimeout(
      client.checkAuthorization(),
      TELEGRAM_CONNECT_TIMEOUT_MS,
      'Проверка импортированной Telegram Web-сессии'
    ).catch(() => false);
    saveTelegramClientSession(client);
    if (!authorized) {
      throw Object.assign(new Error('Telegram Web-сессия импортирована, но Telegram не признал её авторизованной для MTProto.'), {
        code: 'TELEGRAM_WEB_SESSION_UNAUTHORIZED'
      });
    }
    return {
      ok: true,
      authorized: true,
      connected: true,
      hasSession: true,
      importedFromWeb: true,
      dcId: extracted.dcId,
      proxyLabel: proxyLabel || '',
      proxyMode: proxyMode || '',
      fakeTlsDomain: fakeTlsDomain || ''
    };
  } catch (error) {
    await disconnectTelegramClient();
    setStoredTelegramSessionString(previousSessionString);
    return buildTelegramErrorPayload(error, 'TELEGRAM_WEB_SESSION_IMPORT_ERROR');
  }
}

async function scrapeTelegramWebDialogs(payload = {}, options = {}) {
  const settings = normalizeTelegramApiSettings(payload?.settings || payload);
  const validation = validateTelegramApiSettings(settings);
  if (!validation.ok) {
    return buildTelegramErrorPayload(Object.assign(new Error(validation.error), {
      code: validation.code || 'TELEGRAM_SETTINGS_INVALID'
    }), 'TELEGRAM_WEB_DIALOGS_ERROR');
  }

  await openTelegramWebWindow({ settings }, {
    show: options.showWindow === true,
    focus: options.showWindow === true
  });
  if (!telegramWebWindow || telegramWebWindow.isDestroyed()) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_NOT_OPEN',
      error: 'Откройте Telegram Web и войдите в аккаунт, затем обновите диалоги.'
    };
  }

  let scrapeResult = null;
  const attempts = Math.max(1, Math.min(18, Math.trunc(Number(options.attempts || 12)) || 12));
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    try {
      scrapeResult = await telegramWebWindow.webContents.executeJavaScript(TELEGRAM_WEB_DIALOG_SCRAPE_SCRIPT, true);
      if (Array.isArray(scrapeResult?.dialogs) && scrapeResult.dialogs.length) {
        break;
      }
      if (scrapeResult?.loginVisible === true && attempt >= 2) {
        break;
      }
    } catch (error) {
      if (attempt >= 2) {
        return buildTelegramErrorPayload(error, 'TELEGRAM_WEB_DIALOGS_ERROR');
      }
    }
    await waitForTelegramMs(1000);
  }

  const dialogs = (Array.isArray(scrapeResult?.dialogs) ? scrapeResult.dialogs : [])
    .map((dialog, index) => normalizeTelegramWebDialog(dialog, index))
    .filter(Boolean);
  if (!dialogs.length) {
    const webAuthMessage = options.showWindow === true
      ? 'Telegram Web открыт. Войдите в аккаунт в этом окне, затем нажмите «Обновить диалоги».'
      : 'Откройте Telegram Web, войдите в аккаунт, затем нажмите «Обновить диалоги».';
    return {
      ok: false,
      code: scrapeResult?.loginVisible === true ? 'TELEGRAM_WEB_AUTH_REQUIRED' : 'TELEGRAM_WEB_DIALOGS_EMPTY',
      error: scrapeResult?.loginVisible === true
        ? webAuthMessage
        : 'Не удалось прочитать список диалогов Telegram Web. Откройте список чатов в окне Telegram Web и повторите обновление.',
      webMode: true,
      authorized: false
    };
  }

  telegramWebDialogCache = dialogs;
  telegramWebDialogCacheUpdatedAt = Date.now();
  return {
    ok: true,
    authorized: true,
    webMode: true,
    proxyLabel: validation.proxyLabel || '',
    proxyMode: validation.proxyMode || '',
    fakeTlsDomain: validation.fakeTlsDomain || '',
    dialogs,
    loadedAt: telegramWebDialogCacheUpdatedAt
  };
}

async function selectTelegramWebDialog(payload = {}, options = {}) {
  const settings = normalizeTelegramApiSettings(payload?.settings || payload);
  const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
  const dialog = getTelegramWebDialogByChatId(chatId);
  if (!dialog) {
    await scrapeTelegramWebDialogs(payload, {
      showWindow: options.showWindow === true,
      attempts: 3
    }).catch(() => null);
  }
  const resolvedDialog = getTelegramWebDialogByChatId(chatId);
  if (!resolvedDialog) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_DIALOG_NOT_FOUND',
      error: 'Не нашёл этот диалог в Telegram Web. Откройте список чатов и обновите диалоги.'
    };
  }
  await openTelegramWebWindow({ settings }, {
    show: options.showWindow === true,
    focus: options.focusWindow === true,
    preserveCurrent: true
  });
  if (!telegramWebWindow || telegramWebWindow.isDestroyed()) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_NOT_OPEN',
      error: 'Откройте Telegram Web и войдите в аккаунт.'
    };
  }
  const result = await telegramWebWindow.webContents.executeJavaScript(
    buildTelegramWebExecutorScript(TELEGRAM_WEB_SELECT_DIALOG_EXECUTOR, {
      id: resolvedDialog.id,
      title: resolvedDialog.title,
      href: resolvedDialog.webHref || ''
    }),
    true
  );
  if (!result?.ok) {
    return {
      ok: false,
      code: 'TELEGRAM_WEB_DIALOG_NOT_FOUND',
      error: cleanTelegramText(result?.error || 'Не удалось открыть диалог Telegram Web.', 260)
    };
  }
  await waitForTelegramMs(Math.max(120, Math.min(1500, Math.trunc(Number(options.waitAfterSelectMs || 450)) || 450)));
  return {
    ok: true,
    dialog: resolvedDialog,
    result
  };
}

function normalizeTelegramWebMessage(rawMessage = null, chatId = '') {
  if (!rawMessage || typeof rawMessage !== 'object') return null;
  const normalizedChatId = normalizeTelegramChatId(chatId || '');
  const text = cleanTelegramMultiline(rawMessage.text || '', 6000);
  const hasMedia = rawMessage.hasMedia === true;
  const isCallService = rawMessage.serviceKind === 'telegram_call' || rawMessage.attachmentLabel === 'Звонок';
  if (!text && !hasMedia && !isCallService) return null;
  const timestamp = Math.max(0, Number(rawMessage.timestamp || Date.now()) || Date.now());
  const id = cleanTelegramText(rawMessage.id || `web-${timestamp}`, 120);
  const isMine = rawMessage.isMine === true;
  const authorName = cleanTelegramText(rawMessage.authorName || (isMine ? 'Вы' : 'Telegram'), 160);
  const attachmentLabel = isCallService ? 'Звонок' : '';
  const displayText = text || (isCallService ? (isMine ? 'Исходящий звонок' : 'Входящий звонок') : (hasMedia ? 'Вложение Telegram Web' : ''));
  return {
    id,
    workspaceId: 'telegram',
    chatId: normalizedChatId,
    text: displayText,
    formattedText: displayText,
    authorName,
    authorMemberId: isMine ? 'telegram:self' : 'telegram:web',
    authorAvatarUrl: '',
    timestamp,
    isMine,
    isSystem: isCallService,
    deliveryStatus: isMine ? 'sent' : '',
    readByMemberIds: [],
    replyToMessageId: '',
    threadChatId: '',
    threadTitle: '',
    threadMessageCount: 0,
    attachments: [],
    raw: {
      source: 'telegram-web',
      content: displayText ? [{ markdown: displayText }] : [],
      attachmentLabel,
      systemSignal: isCallService ? 'telegram_phone_call' : ''
    }
  };
}

async function listTelegramWebMessages(payload = {}) {
  try {
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    const selected = await selectTelegramWebDialog(payload, {
      showWindow: payload?.showWindow === true,
      focusWindow: payload?.focusWindow === true,
      waitAfterSelectMs: 700
    });
    if (!selected?.ok) return selected;
    const count = Math.max(1, Math.min(200, Math.trunc(Number(payload?.count || payload?.limit || 80) || 80)));
    let scrapeResult = null;
    for (let attempt = 0; attempt < 6; attempt += 1) {
      scrapeResult = await telegramWebWindow.webContents.executeJavaScript(
        buildTelegramWebExecutorScript(TELEGRAM_WEB_MESSAGES_EXECUTOR, { count, limit: count }),
        true
      );
      if (Array.isArray(scrapeResult?.items) && scrapeResult.items.length) break;
      await waitForTelegramMs(350);
    }
    const items = (Array.isArray(scrapeResult?.items) ? scrapeResult.items : [])
      .map((message) => normalizeTelegramWebMessage(message, chatId))
      .filter(Boolean)
      .sort((left, right) => Number(left.timestamp || 0) - Number(right.timestamp || 0));
    return {
      ok: true,
      authorized: true,
      webMode: true,
      items,
      hasMore: false,
      loadedCount: count,
      resolvedChatId: chatId,
      resolvedWorkspaceId: 'telegram'
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_WEB_MESSAGES_ERROR');
  }
}

async function sendTelegramWebMessage(payload = {}) {
  try {
    const chatId = normalizeTelegramChatId(payload?.chatId || payload?.peer || '');
    const text = cleanTelegramMultiline(payload?.text || payload?.message || '', 6000);
    if (!text) {
      return {
        ok: false,
        code: 'TELEGRAM_MESSAGE_EMPTY',
        error: 'Не удалось отправить пустое Telegram-сообщение.'
      };
    }
    const selected = await selectTelegramWebDialog(payload, {
      showWindow: payload?.showWindow === true,
      focusWindow: payload?.focusWindow === true,
      waitAfterSelectMs: 400
    });
    if (!selected?.ok) return selected;
    const result = await telegramWebWindow.webContents.executeJavaScript(
      buildTelegramWebExecutorScript(TELEGRAM_WEB_SEND_TEXT_EXECUTOR, { text }),
      true
    );
    if (!result?.ok) {
      return {
        ok: false,
        code: 'TELEGRAM_WEB_SEND_ERROR',
        error: cleanTelegramText(result?.error || 'Telegram Web не отправил сообщение.', 260)
      };
    }
    const message = normalizeTelegramWebMessage({
      id: `web-local-${Date.now()}`,
      text,
      authorName: 'Вы',
      isMine: true,
      timestamp: Date.now()
    }, chatId);
    return {
      ok: true,
      webMode: true,
      message
    };
  } catch (error) {
    return buildTelegramErrorPayload(error, 'TELEGRAM_WEB_SEND_ERROR');
  }
}

async function markTelegramWebChatAsRead(payload = {}) {
  const selected = await selectTelegramWebDialog(payload, {
    showWindow: false,
    focusWindow: false,
    waitAfterSelectMs: 150
  });
  return selected?.ok
    ? { ok: true, webMode: true }
    : selected;
}

async function openTelegramWebWindow(payload = {}, options = {}) {
  const peer = cleanTelegramText(payload?.peer || payload?.username || '', 180);
  const settings = normalizeTelegramApiSettings(payload?.settings || payload);
  const proxyResult = parseTelegramProxyUrl(settings.proxyUrl);
  if (settings.proxyUrl && !proxyResult.ok) {
    return {
      ok: false,
      code: 'TELEGRAM_PROXY_INVALID',
      error: proxyResult.error || 'Некорректная ссылка Telegram proxy.'
    };
  }
  const targetUrl = proxyResult.ok && proxyResult.normalizedProxyUrl
    ? `${TELEGRAM_WEB_URL}#?tgaddr=${encodeURIComponent(proxyResult.normalizedProxyUrl)}`
    : TELEGRAM_WEB_URL;
  const shouldShow = options.show !== false;
  const shouldFocus = shouldShow && options.focus !== false;
  const preserveCurrent = options.preserveCurrent === true;
  if (telegramWebWindow && !telegramWebWindow.isDestroyed()) {
    if (shouldShow && telegramWebWindow.isMinimized()) {
      telegramWebWindow.restore();
    }
    if (shouldShow && !telegramWebWindow.isVisible()) {
      telegramWebWindow.show();
    }
    if (shouldFocus) {
      telegramWebWindow.focus();
    }
    const currentUrl = telegramWebWindow.webContents.getURL();
    const currentIsTelegramWeb = /^https:\/\/web\.telegram\.org\/a\/?/iu.test(currentUrl || '');
    if ((!preserveCurrent || !currentIsTelegramWeb) && currentUrl !== targetUrl) {
      await telegramWebWindow.loadURL(targetUrl);
    }
    return { ok: true, reused: true, peer, webMode: true };
  }

  telegramWebWindow = new BrowserWindow({
    width: 1180,
    height: 820,
    minWidth: 900,
    minHeight: 640,
    show: false,
    title: 'Telegram Web',
    backgroundColor: '#ffffff',
    webPreferences: {
      partition: 'persist:telegram-web',
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: true,
      webSecurity: true,
      additionalArguments: ['--yu-window-role=telegram-web']
    }
  });
  telegramWebWindow.setTitle('Telegram Web');
  if (shouldShow) {
    telegramWebWindow.once('ready-to-show', () => {
      if (!telegramWebWindow || telegramWebWindow.isDestroyed()) return;
      telegramWebWindow.show();
      if (shouldFocus) {
        telegramWebWindow.focus();
      }
    });
  }
  telegramWebWindow.on('closed', () => {
    telegramWebWindow = null;
  });
  await telegramWebWindow.loadURL(targetUrl);
  return { ok: true, reused: false, peer, webMode: true };
}

function getMediaAccessStatusSafe(mediaType = 'microphone') {
  if (!systemPreferences || typeof systemPreferences.getMediaAccessStatus !== 'function') {
    return 'unknown';
  }
  try {
    return String(systemPreferences.getMediaAccessStatus(mediaType) || 'unknown').trim() || 'unknown';
  } catch {
    return 'unknown';
  }
}

function getScreenCaptureAccessStatus() {
  if (process.platform !== 'darwin') {
    return 'granted';
  }
  return getMediaAccessStatusSafe('screen');
}

async function requestMediaAccessSafe(mediaType = 'microphone') {
  const status = getMediaAccessStatusSafe(mediaType);
  if (status === 'granted') {
    return { granted: true, status };
  }
  if (process.platform === 'darwin' && typeof systemPreferences?.askForMediaAccess === 'function') {
    try {
      const granted = await systemPreferences.askForMediaAccess(mediaType);
      return {
        granted: granted === true,
        status: getMediaAccessStatusSafe(mediaType)
      };
    } catch {
      return { granted: false, status: getMediaAccessStatusSafe(mediaType) };
    }
  }
  return {
    granted: status !== 'denied' && status !== 'restricted',
    status
  };
}

async function getPreferredDesktopCaptureSource() {
  const sources = await desktopCapturer.getSources({
    types: ['screen', 'window'],
    thumbnailSize: { width: 0, height: 0 },
    fetchWindowIcons: false
  });
  return sources.find((source) => String(source?.id || '').startsWith('screen:'))
    || sources[0]
    || null;
}

const ZIP_CRC32_TABLE = (() => {
  const table = new Uint32Array(256);
  for (let index = 0; index < 256; index += 1) {
    let value = index;
    for (let bit = 0; bit < 8; bit += 1) {
      value = (value & 1) === 1
        ? (0xEDB88320 ^ (value >>> 1))
        : (value >>> 1);
    }
    table[index] = value >>> 0;
  }
  return table;
})();

function computeZipCrc32(buffer = Buffer.alloc(0)) {
  const source = Buffer.isBuffer(buffer) ? buffer : Buffer.from(buffer);
  let crc = 0xFFFFFFFF;
  for (let index = 0; index < source.length; index += 1) {
    crc = ZIP_CRC32_TABLE[(crc ^ source[index]) & 0xFF] ^ (crc >>> 8);
  }
  return (crc ^ 0xFFFFFFFF) >>> 0;
}

function normalizeArchiveEntryPath(entryPath = '') {
  const normalized = String(entryPath || '')
    .replace(/\\/g, '/')
    .split('/')
    .map((segment) => String(segment || '').trim())
    .filter((segment) => segment && segment !== '.' && segment !== '..')
    .join('/');
  return normalized.replace(/^\/+/, '');
}

function resolveArchiveEntryBuffer(entry = {}) {
  if (Buffer.isBuffer(entry?.contents)) {
    return Buffer.from(entry.contents);
  }
  const encoding = String(entry?.encoding || 'utf8').trim().toLowerCase() === 'base64' ? 'base64' : 'utf8';
  return Buffer.from(String(entry?.contents || ''), encoding);
}

function resolveZipDosDateTime(value = Date.now()) {
  let date = new Date(value);
  if (!Number.isFinite(date.getTime())) {
    date = new Date();
  }
  if (date.getFullYear() < 1980) {
    date = new Date(1980, 0, 1, 0, 0, 0);
  } else if (date.getFullYear() > 2107) {
    date = new Date(2107, 11, 31, 23, 59, 58);
  }
  return {
    dosDate: (((date.getFullYear() - 1980) & 0x7F) << 9) | ((date.getMonth() + 1) << 5) | date.getDate(),
    dosTime: (date.getHours() << 11) | (date.getMinutes() << 5) | Math.floor(date.getSeconds() / 2)
  };
}

function buildZipArchive(entries = []) {
  const safeEntries = Array.isArray(entries) ? entries : [];
  if (safeEntries.length > 0xFFFF) {
    const error = new Error('Слишком много файлов для ZIP-архива');
    error.code = 'EXPORT_ARCHIVE_TOO_MANY_FILES';
    throw error;
  }

  const preparedEntries = safeEntries.map((entry, index) => {
    const descriptor = isPlainRecord(entry) ? entry : {};
    const archivePath = normalizeArchiveEntryPath(descriptor.path || descriptor.name || '');
    if (!archivePath) {
      const error = new Error(`Некорректный путь для файла архива #${index + 1}`);
      error.code = 'EXPORT_ARCHIVE_INVALID_PATH';
      throw error;
    }
    const fileName = Buffer.from(archivePath, 'utf8');
    if (fileName.length > 0xFFFF) {
      const error = new Error(`Слишком длинное имя файла в архиве: ${archivePath}`);
      error.code = 'EXPORT_ARCHIVE_FILENAME_TOO_LONG';
      throw error;
    }

    const rawContents = resolveArchiveEntryBuffer(descriptor);
    if (rawContents.length > 0xFFFFFFFF) {
      const error = new Error(`Файл слишком большой для ZIP-архива: ${archivePath}`);
      error.code = 'EXPORT_ARCHIVE_FILE_TOO_LARGE';
      throw error;
    }

    const deflatedContents = rawContents.length ? zlib.deflateRawSync(rawContents) : Buffer.alloc(0);
    const useCompression = deflatedContents.length > 0 && deflatedContents.length < rawContents.length;
    const fileContents = useCompression ? deflatedContents : rawContents;
    const { dosDate, dosTime } = resolveZipDosDateTime(descriptor.mtime || descriptor.modifiedAt || descriptor.timestamp || Date.now());
    return {
      fileName,
      fileContents,
      compressedSize: fileContents.length,
      uncompressedSize: rawContents.length,
      compressionMethod: useCompression ? 8 : 0,
      crc32: computeZipCrc32(rawContents),
      flags: 0x0800,
      dosDate,
      dosTime
    };
  });

  const localChunks = [];
  const centralChunks = [];
  let offset = 0;

  preparedEntries.forEach((entry) => {
    if (entry.compressedSize > 0xFFFFFFFF || offset > 0xFFFFFFFF) {
      const error = new Error('ZIP-архив слишком большой');
      error.code = 'EXPORT_ARCHIVE_TOO_LARGE';
      throw error;
    }

    const localHeader = Buffer.alloc(30 + entry.fileName.length);
    localHeader.writeUInt32LE(0x04034B50, 0);
    localHeader.writeUInt16LE(20, 4);
    localHeader.writeUInt16LE(entry.flags, 6);
    localHeader.writeUInt16LE(entry.compressionMethod, 8);
    localHeader.writeUInt16LE(entry.dosTime, 10);
    localHeader.writeUInt16LE(entry.dosDate, 12);
    localHeader.writeUInt32LE(entry.crc32, 14);
    localHeader.writeUInt32LE(entry.compressedSize, 18);
    localHeader.writeUInt32LE(entry.uncompressedSize, 22);
    localHeader.writeUInt16LE(entry.fileName.length, 26);
    localHeader.writeUInt16LE(0, 28);
    entry.fileName.copy(localHeader, 30);
    localChunks.push(localHeader, entry.fileContents);

    const centralHeader = Buffer.alloc(46 + entry.fileName.length);
    centralHeader.writeUInt32LE(0x02014B50, 0);
    centralHeader.writeUInt16LE(20, 4);
    centralHeader.writeUInt16LE(20, 6);
    centralHeader.writeUInt16LE(entry.flags, 8);
    centralHeader.writeUInt16LE(entry.compressionMethod, 10);
    centralHeader.writeUInt16LE(entry.dosTime, 12);
    centralHeader.writeUInt16LE(entry.dosDate, 14);
    centralHeader.writeUInt32LE(entry.crc32, 16);
    centralHeader.writeUInt32LE(entry.compressedSize, 20);
    centralHeader.writeUInt32LE(entry.uncompressedSize, 24);
    centralHeader.writeUInt16LE(entry.fileName.length, 28);
    centralHeader.writeUInt16LE(0, 30);
    centralHeader.writeUInt16LE(0, 32);
    centralHeader.writeUInt16LE(0, 34);
    centralHeader.writeUInt16LE(0, 36);
    centralHeader.writeUInt32LE(0, 38);
    centralHeader.writeUInt32LE(offset, 42);
    entry.fileName.copy(centralHeader, 46);
    centralChunks.push(centralHeader);

    offset += localHeader.length + entry.fileContents.length;
  });

  const centralDirectorySize = centralChunks.reduce((total, chunk) => total + chunk.length, 0);
  if (centralDirectorySize > 0xFFFFFFFF || offset > 0xFFFFFFFF) {
    const error = new Error('ZIP-архив слишком большой');
    error.code = 'EXPORT_ARCHIVE_TOO_LARGE';
    throw error;
  }

  const endRecord = Buffer.alloc(22);
  endRecord.writeUInt32LE(0x06054B50, 0);
  endRecord.writeUInt16LE(0, 4);
  endRecord.writeUInt16LE(0, 6);
  endRecord.writeUInt16LE(preparedEntries.length, 8);
  endRecord.writeUInt16LE(preparedEntries.length, 10);
  endRecord.writeUInt32LE(centralDirectorySize, 12);
  endRecord.writeUInt32LE(offset, 16);
  endRecord.writeUInt16LE(0, 20);

  return Buffer.concat([...localChunks, ...centralChunks, endRecord]);
}

async function saveExportFile(payload = {}) {
  const defaultPath = String(payload?.defaultPath || 'export.txt').trim() || 'export.txt';
  const title = String(payload?.title || 'Сохранить экспорт').trim() || 'Сохранить экспорт';
  const filters = Array.isArray(payload?.filters) ? payload.filters : [];
  const contents = String(payload?.contents || '');
  const encoding = String(payload?.encoding || 'utf8').trim().toLowerCase() === 'base64' ? 'base64' : 'utf8';
  const result = await dialog.showSaveDialog(getDialogOwnerWindow(), {
    title,
    defaultPath,
    filters
  });
  if (result.canceled || !result.filePath) {
    return { canceled: true, filePath: '' };
  }
  if (encoding === 'base64') {
    fs.writeFileSync(result.filePath, Buffer.from(contents, 'base64'));
  } else {
    fs.writeFileSync(result.filePath, contents, 'utf8');
  }
  return { canceled: false, filePath: result.filePath };
}

async function saveExportArchive(payload = {}) {
  const defaultPath = String(payload?.defaultPath || 'export.zip').trim() || 'export.zip';
  const title = String(payload?.title || 'Сохранить архив').trim() || 'Сохранить архив';
  const filters = Array.isArray(payload?.filters) && payload.filters.length
    ? payload.filters
    : [{ name: 'ZIP', extensions: ['zip'] }];
  const entries = Array.isArray(payload?.entries) ? payload.entries : [];
  const result = await dialog.showSaveDialog(getDialogOwnerWindow(), {
    title,
    defaultPath,
    filters
  });
  if (result.canceled || !result.filePath) {
    return { canceled: true, filePath: '' };
  }
  const zipBuffer = buildZipArchive(entries);
  fs.writeFileSync(result.filePath, zipBuffer);
  return { canceled: false, filePath: result.filePath };
}

async function openImportFile(payload = {}) {
  const title = String(payload?.title || 'Открыть файл импорта').trim() || 'Открыть файл импорта';
  const filters = Array.isArray(payload?.filters) ? payload.filters : [];
  const encoding = String(payload?.encoding || 'utf8').trim().toLowerCase() === 'base64' ? 'base64' : 'utf8';
  const result = await dialog.showOpenDialog(getDialogOwnerWindow(), {
    title,
    filters,
    properties: ['openFile']
  });
  const filePath = Array.isArray(result?.filePaths) ? String(result.filePaths[0] || '').trim() : '';
  if (result?.canceled || !filePath) {
    return {
      canceled: true,
      filePath: '',
      fileName: '',
      text: '',
      error: ''
    };
  }
  try {
    const buffer = fs.readFileSync(filePath);
    return {
      canceled: false,
      filePath,
      fileName: path.basename(filePath),
      text: encoding === 'base64' ? buffer.toString('base64') : buffer.toString('utf8'),
      error: ''
    };
  } catch (error) {
    return {
      canceled: false,
      filePath,
      fileName: path.basename(filePath),
      text: '',
      error: String(error?.message || 'Не удалось прочитать файл')
    };
  }
}

async function saveExportPdf(payload = {}) {
  const html = String(payload?.html || '');
  if (!html) {
    const error = new Error('HTML для PDF пустой');
    error.code = 'EXPORT_PDF_EMPTY_HTML';
    throw error;
  }
  const defaultPath = String(payload?.defaultPath || 'export.pdf').trim() || 'export.pdf';
  const title = String(payload?.title || 'Сохранить PDF').trim() || 'Сохранить PDF';
  const result = await dialog.showSaveDialog(getDialogOwnerWindow(), {
    title,
    defaultPath,
    filters: [{ name: 'PDF', extensions: ['pdf'] }]
  });
  if (result.canceled || !result.filePath) {
    return { canceled: true, filePath: '' };
  }

  let exportWindow = null;
  try {
    exportWindow = new BrowserWindow({
      show: false,
      width: 1100,
      height: 1400,
      backgroundColor: '#ffffff',
      webPreferences: {
        sandbox: true,
        contextIsolation: true
      }
    });
    await exportWindow.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(html)}`);
    const pdfBuffer = await exportWindow.webContents.printToPDF({
      printBackground: true,
      pageSize: 'A4',
      margins: {
        top: 0,
        bottom: 0,
        left: 0,
        right: 0
      }
    });
    fs.writeFileSync(result.filePath, pdfBuffer);
    return { canceled: false, filePath: result.filePath };
  } finally {
    if (exportWindow && !exportWindow.isDestroyed()) {
      exportWindow.destroy();
    }
  }
}

function getMainWindowStateFilePath() {
  try {
    return path.join(app.getPath('userData'), WINDOW_STATE_FILE_NAME);
  } catch {
    return path.join(__dirname, WINDOW_STATE_FILE_NAME);
  }
}

function normalizeWindowMode(value = '') {
  return String(value || '').trim().toLowerCase() === WINDOW_MODE_MESSENGER
    ? WINDOW_MODE_MESSENGER
    : WINDOW_MODE_NORMAL;
}

function normalizeWindowOpacity(value = DEFAULT_MESSENGER_OPACITY) {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) {
    return DEFAULT_MESSENGER_OPACITY;
  }
  return Math.min(
    MAX_MESSENGER_OPACITY,
    Math.max(MIN_MESSENGER_OPACITY, Math.round(numeric * 100) / 100)
  );
}

function normalizeMessengerAnimationDuration(value = DEFAULT_MESSENGER_ANIMATION_DURATION_MS) {
  const numeric = Math.round(Number(value) || 0);
  if (!Number.isFinite(numeric) || numeric <= 0) {
    return DEFAULT_MESSENGER_ANIMATION_DURATION_MS;
  }
  return Math.min(
    MAX_MESSENGER_ANIMATION_DURATION_MS,
    Math.max(MIN_MESSENGER_ANIMATION_DURATION_MS, numeric)
  );
}

function normalizePersistedWindowBounds(bounds = null, options = {}) {
  if (!bounds || typeof bounds !== 'object') return null;
  const minWidth = Math.max(320, Number(options?.minWidth) || 320);
  const minHeight = Math.max(240, Number(options?.minHeight) || 240);
  const width = Math.max(minWidth, Math.round(Number(bounds.width) || 0));
  const height = Math.max(minHeight, Math.round(Number(bounds.height) || 0));
  const x = Number(bounds.x);
  const y = Number(bounds.y);
  if (!width || !height || !Number.isFinite(x) || !Number.isFinite(y)) {
    return null;
  }
  return {
    x: Math.round(x),
    y: Math.round(y),
    width,
    height
  };
}

function isLegacyDefaultMainWindowBounds(bounds = null) {
  const width = Math.round(Number(bounds?.width) || 0);
  const height = Math.round(Number(bounds?.height) || 0);
  if (!width || !height) return false;
  return (
    (width === 1440 && height === 900)
    || (width === 1280 && height === 820)
    || (width === 1200 && height === 800)
  );
}

function shouldRestoreSavedMainWindowBounds(savedState = null) {
  if (!savedState || typeof savedState !== 'object') return false;
  if (savedState.boundsCustomized === true) return true;
  const candidateBounds = savedState?.normalBounds && typeof savedState.normalBounds === 'object'
    ? savedState.normalBounds
    : savedState;
  return !isLegacyDefaultMainWindowBounds(candidateBounds) && !isLegacyDefaultMainWindowBounds(savedState);
}

function shortcutTokenToAccelerator(shortcut = '') {
  const normalized = normalizeKeyboardShortcut(shortcut);
  if (!normalized) return '';
  const keyMap = new Map([
    ['cmd', 'CommandOrControl'],
    ['ctrl', 'Control'],
    ['alt', 'Alt'],
    ['shift', 'Shift'],
    ['space', 'Space'],
    ['esc', 'Escape'],
    ['up', 'Up'],
    ['down', 'Down'],
    ['left', 'Left'],
    ['right', 'Right'],
    ['tab', 'Tab'],
    ['enter', 'Enter'],
    ['return', 'Enter'],
    ['backspace', 'Backspace'],
    ['delete', 'Delete'],
    ['home', 'Home'],
    ['end', 'End'],
    ['pageup', 'PageUp'],
    ['pagedown', 'PageDown']
  ]);

  return normalized
    .split('+')
    .map((part) => {
      const token = String(part || '').trim().toLowerCase();
      if (!token) return '';
      if (keyMap.has(token)) {
        return keyMap.get(token);
      }
      if (/^f\d{1,2}$/i.test(token)) {
        return token.toUpperCase();
      }
      if (token.length === 1) {
        return token.toUpperCase();
      }
      return token.charAt(0).toUpperCase() + token.slice(1);
    })
    .filter(Boolean)
    .join('+');
}

function getDisplayForWindowBounds(bounds = null) {
  try {
    const safeBounds = normalizePersistedWindowBounds(bounds);
    if (safeBounds) {
      return screen.getDisplayMatching(safeBounds);
    }
    return screen.getPrimaryDisplay();
  } catch {
    return null;
  }
}

function isCollapsedMessengerWindowBounds(bounds = null) {
  return Boolean(bounds && Number(bounds.height) <= (MESSENGER_WINDOW_COLLAPSED_HEIGHT + 2));
}

function resolveMessengerExpandedBounds(sourceBounds = null) {
  const candidates = [
    sourceBounds,
    messengerWindowExpandedBounds,
    mainWindowNormalBounds
  ];

  for (const candidate of candidates) {
    const safeBounds = normalizePersistedWindowBounds(candidate, {
      minWidth: 1,
      minHeight: 1
    });
    if (!safeBounds || isCollapsedMessengerWindowBounds(safeBounds)) continue;
    const display = getDisplayForWindowBounds(safeBounds);
    const screenBounds = display?.bounds && typeof display.bounds === 'object'
      ? display.bounds
      : { y: 0 };
    return {
      ...safeBounds,
      y: Math.round(Number(screenBounds.y) || 0)
    };
  }

  return null;
}

function buildMessengerWindowBounds(sourceBounds = null) {
  const expandedBounds = resolveMessengerExpandedBounds(sourceBounds);
  if (expandedBounds) {
    return expandedBounds;
  }
  const display = getDisplayForWindowBounds(sourceBounds);
  const screenBounds = display?.bounds && typeof display.bounds === 'object'
    ? display.bounds
    : { x: 0, y: 0, width: 1440, height: 900 };
  const availableWidth = Math.max(320, Math.round(Number(screenBounds.width) || 1440));
  const availableHeight = Math.max(320, Math.round(Number(screenBounds.height) || 900));
  const preferredHeight = Math.round(availableHeight * MESSENGER_WINDOW_HEIGHT_RATIO);
  return {
    x: Math.round(Number(screenBounds.x) || 0),
    y: Math.round(Number(screenBounds.y) || 0),
    width: availableWidth,
    height: Math.max(Math.min(MESSENGER_WINDOW_MIN_HEIGHT, availableHeight), Math.min(availableHeight, preferredHeight))
  };
}

function buildHiddenMessengerWindowBounds(sourceBounds = null) {
  const visibleBounds = buildMessengerWindowBounds(sourceBounds);
  return {
    ...visibleBounds,
    y: Math.round(visibleBounds.y - visibleBounds.height + MESSENGER_WINDOW_HIDE_PEEK_PX)
  };
}

function buildCollapsedMessengerWindowBounds(sourceBounds = null) {
  const visibleBounds = buildMessengerWindowBounds(sourceBounds);
  return {
    ...visibleBounds,
    height: MESSENGER_WINDOW_COLLAPSED_HEIGHT
  };
}

function buildFullyHiddenWindowBounds(bounds = null) {
  const safeBounds = normalizePersistedWindowBounds(bounds, {
    minWidth: 1,
    minHeight: 1
  });
  if (!safeBounds) return null;
  const display = getDisplayForWindowBounds(safeBounds);
  const screenBounds = display?.bounds && typeof display.bounds === 'object'
    ? display.bounds
    : { x: 0, y: 0 };
  return {
    ...safeBounds,
    y: Math.round((Number(screenBounds.y) || 0) - safeBounds.height + MESSENGER_WINDOW_HIDE_PEEK_PX)
  };
}

function buildCollapsedCurrentWindowBounds(bounds = null) {
  const safeBounds = normalizePersistedWindowBounds(bounds, {
    minWidth: 1,
    minHeight: 1
  });
  if (!safeBounds) return null;
  const display = getDisplayForWindowBounds(safeBounds);
  const screenBounds = display?.bounds && typeof display.bounds === 'object'
    ? display.bounds
    : { y: 0 };
  return {
    ...safeBounds,
    y: Math.round(Number(screenBounds.y) || 0),
    height: MESSENGER_WINDOW_COLLAPSED_HEIGHT
  };
}

function clearMessengerWindowHideTimer(options = {}) {
  if (messengerWindowHideTimer) {
    clearTimeout(messengerWindowHideTimer);
    messengerWindowHideTimer = 0;
  }
  if (options?.preserveDirection !== true) {
    messengerWindowAnimationDirection = '';
  }
}

function getMessengerWindowShellState() {
  return {
    mode: normalizeWindowMode(messengerWindowMode),
    shortcut: normalizeKeyboardShortcut(messengerWindowShortcut || DEFAULT_MESSENGER_SHORTCUT) || DEFAULT_MESSENGER_SHORTCUT,
    opacity: normalizeWindowOpacity(messengerWindowOpacity),
    animationDurationMs: normalizeMessengerAnimationDuration(messengerWindowAnimationDurationMs),
    shortcutRegistered: Boolean(registeredMessengerWindowShortcut)
  };
}

function broadcastMessengerWindowShellState() {
  if (!(mainWindow instanceof BrowserWindow) || mainWindow.isDestroyed()) return;
  try {
    mainWindow.webContents.send('yuchat-window-shell-state', getMessengerWindowShellState());
  } catch {
    // ignore renderer bridge failures
  }
}

function applyMessengerWindowOpacity(windowRef = mainWindow) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  try {
    windowRef.setOpacity(normalizeWindowOpacity(messengerWindowOpacity));
  } catch {
    // ignore opacity updates on unsupported platforms
  }
}

function applyMainWindowMinimumSize(windowRef = mainWindow, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  const messengerMode = options?.messengerMode === true;
  const minWidth = messengerMode ? MESSENGER_WINDOW_MIN_WIDTH : MAIN_WINDOW_MIN_WIDTH;
  const minHeight = messengerMode ? MESSENGER_WINDOW_COLLAPSED_HEIGHT : MAIN_WINDOW_MIN_HEIGHT;
  try {
    windowRef.setMinimumSize(minWidth, minHeight);
  } catch {
    // ignore minimum size update failures
  }
}

function detachWindowForFreeformAnimation(windowRef = mainWindow, bounds = null) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  const movableBounds = normalizePersistedWindowBounds(bounds, {
    minWidth: 320,
    minHeight: 240
  }) || normalizePersistedWindowBounds(windowRef.getBounds(), {
    minWidth: 320,
    minHeight: 240
  });

  try {
    if (windowRef.isFullScreen()) {
      windowRef.setFullScreen(false);
    }
  } catch {
    // ignore fullscreen transition failures
  }
  try {
    if (windowRef.isMaximized()) {
      windowRef.unmaximize();
    }
  } catch {
    // ignore maximize reset failures
  }
  if (movableBounds) {
    try {
      windowRef.setBounds(movableBounds, false);
    } catch {
      // ignore movable bounds restore failures
    }
  }
}

function captureMainWindowNormalState(windowRef = mainWindow) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  const bounds = normalizePersistedWindowBounds(
    typeof windowRef.getNormalBounds === 'function'
      ? windowRef.getNormalBounds()
      : windowRef.getBounds(),
    {
      minWidth: MAIN_WINDOW_MIN_WIDTH,
      minHeight: MAIN_WINDOW_MIN_HEIGHT
    }
  );
  if (bounds) {
    mainWindowNormalBounds = bounds;
  }
  mainWindowNormalIsMaximized = windowRef.isMaximized();
}

function getMainWindowStateSnapshot(windowRef = mainWindow) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return null;
  const liveBounds = windowRef.getBounds();
  const persistedBounds = normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER
    ? (resolveMessengerExpandedBounds(messengerWindowExpandedBounds || liveBounds) || buildMessengerWindowBounds(mainWindowNormalBounds || liveBounds))
    : {
        x: Math.round(Number(liveBounds.x) || 0),
        y: Math.round(Number(liveBounds.y) || 0),
        width: Math.max(MAIN_WINDOW_MIN_WIDTH, Math.round(Number(liveBounds.width) || 0) || MAIN_WINDOW_MIN_WIDTH),
        height: Math.max(MAIN_WINDOW_MIN_HEIGHT, Math.round(Number(liveBounds.height) || 0) || MAIN_WINDOW_MIN_HEIGHT)
      };
  const safeNormalBounds = normalizePersistedWindowBounds(
    normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER
      ? (mainWindowNormalBounds || null)
      : (typeof windowRef.getNormalBounds === 'function'
        ? windowRef.getNormalBounds()
        : liveBounds),
    { minWidth: MAIN_WINDOW_MIN_WIDTH, minHeight: MAIN_WINDOW_MIN_HEIGHT }
  );
  return {
    ...persistedBounds,
    isMaximized: normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER
      ? false
      : windowRef.isMaximized(),
    boundsCustomized: mainWindowBoundsCustomized === true,
    windowMode: normalizeWindowMode(messengerWindowMode),
    messengerShortcut: normalizeKeyboardShortcut(messengerWindowShortcut || DEFAULT_MESSENGER_SHORTCUT) || DEFAULT_MESSENGER_SHORTCUT,
    messengerOpacity: normalizeWindowOpacity(messengerWindowOpacity),
    messengerAnimationDurationMs: normalizeMessengerAnimationDuration(messengerWindowAnimationDurationMs),
    normalBounds: safeNormalBounds || undefined,
    normalIsMaximized: normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER
      ? mainWindowNormalIsMaximized === true
      : windowRef.isMaximized()
  };
}

function readMainWindowState() {
  try {
    const raw = fs.readFileSync(getMainWindowStateFilePath(), 'utf8');
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') {
      return null;
    }

    const width = Math.max(MAIN_WINDOW_MIN_WIDTH, Number(parsed.width) || 0);
    const height = Math.max(MAIN_WINDOW_MIN_HEIGHT, Number(parsed.height) || 0);
    const x = Number(parsed.x);
    const y = Number(parsed.y);
    const windowMode = normalizeWindowMode(parsed.windowMode || '');
    const normalBounds = normalizePersistedWindowBounds(parsed.normalBounds, {
      minWidth: MAIN_WINDOW_MIN_WIDTH,
      minHeight: MAIN_WINDOW_MIN_HEIGHT
    }) || (
      Number.isFinite(x) && Number.isFinite(y)
        ? {
            x: Math.round(x),
            y: Math.round(y),
            width: width || 1200,
            height: height || 800
          }
        : null
    );
    return {
      width: width || 1200,
      height: height || 800,
      x: Number.isFinite(x) ? Math.round(x) : undefined,
      y: Number.isFinite(y) ? Math.round(y) : undefined,
      isMaximized: parsed.isMaximized === true,
      windowMode,
      boundsCustomized: parsed.boundsCustomized === true,
      messengerShortcut: normalizeKeyboardShortcut(parsed.messengerShortcut || DEFAULT_MESSENGER_SHORTCUT) || DEFAULT_MESSENGER_SHORTCUT,
      messengerOpacity: normalizeWindowOpacity(parsed.messengerOpacity),
      messengerAnimationDurationMs: normalizeMessengerAnimationDuration(parsed.messengerAnimationDurationMs),
      normalBounds,
      normalIsMaximized: parsed.normalIsMaximized === true || (windowMode !== WINDOW_MODE_MESSENGER && parsed.isMaximized === true)
    };
  } catch {
    return null;
  }
}

function persistMainWindowState(windowRef = mainWindow, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  if (windowRef.isMinimized()) return;

  const force = options?.force === true;
  if (mainWindowStatePersistTimer) {
    clearTimeout(mainWindowStatePersistTimer);
    mainWindowStatePersistTimer = 0;
  }

  const writeState = () => {
    if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
    try {
      const payload = getMainWindowStateSnapshot(windowRef);
      if (!payload) return;
      fs.writeFileSync(
        getMainWindowStateFilePath(),
        JSON.stringify(payload, null, 2),
        'utf8'
      );
    } catch {
      // ignore window state persistence failures
    }
  };

  if (force) {
    writeState();
    return;
  }

  mainWindowStatePersistTimer = setTimeout(writeState, 160);
}

function applyMessengerWindowPresentation(windowRef = mainWindow, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  const sourceBounds = options?.sourceBounds || mainWindowNormalBounds || windowRef.getBounds();
  const placementMode = Object.prototype.hasOwnProperty.call(options || {}, 'placement')
    ? String(options?.placement || '').trim().toLowerCase()
    : 'visible';
  const preserveCurrentWindowShape = options?.preserveCurrentWindowShape === true;
  const targetBounds = placementMode === 'hidden'
    ? buildHiddenMessengerWindowBounds(sourceBounds)
    : placementMode === 'visible'
      ? buildMessengerWindowBounds(sourceBounds)
      : null;
  try {
    windowRef.setAlwaysOnTop(true, 'screen-saver');
  } catch {
    try {
      windowRef.setAlwaysOnTop(true);
    } catch {
      // ignore always-on-top failures
    }
  }
  try {
    windowRef.setFullScreenable(false);
  } catch {
    // ignore unsupported fullscreenable updates
  }
  try {
    windowRef.setVisibleOnAllWorkspaces(true, { visibleOnFullScreen: true });
  } catch {
    // ignore workspace visibility failures
  }
  if (!preserveCurrentWindowShape) {
    try {
      if (windowRef.isFullScreen()) {
        windowRef.setFullScreen(false);
      }
    } catch {
      // ignore fullscreen transition failures
    }
    try {
      if (windowRef.isMaximized()) {
        windowRef.unmaximize();
      }
    } catch {
      // ignore maximize reset failures
    }
  }
  if (targetBounds && !preserveCurrentWindowShape) {
    try {
      windowRef.setBounds(targetBounds, options?.animate === true);
    } catch {
      // ignore initial bounds update failures
    }
  }
  applyMessengerWindowOpacity(windowRef);
  if (options?.show !== false) {
    if (!windowRef.isVisible()) {
      windowRef.show();
    }
    try {
      windowRef.moveTop();
    } catch {
      // ignore move-to-top failures
    }
    if (options?.focus !== false) {
      windowRef.focus();
    }
  }
}

function interpolateBounds(fromBounds = {}, toBounds = {}, progress = 1) {
  const t = Math.max(0, Math.min(1, Number(progress) || 0));
  return {
    x: Math.round((Number(fromBounds.x) || 0) + (((Number(toBounds.x) || 0) - (Number(fromBounds.x) || 0)) * t)),
    y: Math.round((Number(fromBounds.y) || 0) + (((Number(toBounds.y) || 0) - (Number(fromBounds.y) || 0)) * t)),
    width: Math.round((Number(fromBounds.width) || 0) + (((Number(toBounds.width) || 0) - (Number(fromBounds.width) || 0)) * t)),
    height: Math.round((Number(fromBounds.height) || 0) + (((Number(toBounds.height) || 0) - (Number(fromBounds.height) || 0)) * t))
  };
}

function easeInOutCubic(value = 0) {
  const t = Math.max(0, Math.min(1, Number(value) || 0));
  return t < 0.5
    ? 4 * t * t * t
    : 1 - Math.pow(-2 * t + 2, 3) / 2;
}

function easeOutCubic(value = 0) {
  const t = Math.max(0, Math.min(1, Number(value) || 0));
  return 1 - Math.pow(1 - t, 3);
}

function easeInCubic(value = 0) {
  const t = Math.max(0, Math.min(1, Number(value) || 0));
  return t * t * t;
}

function resolveMessengerAnimationProgress(progress = 0, direction = '') {
  const t = Math.max(0, Math.min(1, Number(progress) || 0));
  if (String(direction || '').trim().toLowerCase() === 'show') {
    return easeOutCubic(t);
  }
  if (String(direction || '').trim().toLowerCase() === 'hide') {
    return easeInCubic(t);
  }
  return easeInOutCubic(t);
}

function animateMessengerWindowBounds(windowRef, fromBounds = null, toBounds = null, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
    return;
  }

  const startBounds = normalizePersistedWindowBounds(fromBounds, {
    minWidth: 1,
    minHeight: 1
  }) || normalizePersistedWindowBounds(windowRef.getBounds(), {
    minWidth: 1,
    minHeight: 1
  });
  const targetBounds = normalizePersistedWindowBounds(toBounds, {
    minWidth: 1,
    minHeight: 1
  });
  if (!startBounds || !targetBounds) {
    return;
  }

  clearMessengerWindowHideTimer({ preserveDirection: true });
  messengerWindowAnimationDirection = String(options?.direction || '').trim().toLowerCase();
  const durationMs = normalizeMessengerAnimationDuration(
    options?.durationMs ?? messengerWindowAnimationDurationMs
  );
  const useNativeAnimation = options?.useNativeAnimation === true;
  const usePositionOnly = (
    startBounds.width === targetBounds.width
    && startBounds.height === targetBounds.height
    && startBounds.x === targetBounds.x
  );
  const startDelayMs = Math.max(0, Math.round(Number(options?.startDelayMs) || 0));
  let startedAt = 0;

  if (useNativeAnimation) {
    try {
      windowRef.setBounds(startBounds, false);
    } catch {
      // ignore native animation bootstrap failures
    }

    try {
      windowRef.setBounds(targetBounds, true);
    } catch {
      // ignore native animation start failures
    }

    messengerWindowHideTimer = setTimeout(() => {
      messengerWindowHideTimer = 0;
      messengerWindowAnimationDirection = '';
      try {
        windowRef.setBounds(targetBounds, false);
      } catch {
        // ignore final native bounds failures
      }
      if (options?.hideAfter === true) {
        try {
          windowRef.hide();
        } catch {
          // ignore hide failures
        }
      }
      if (options?.focusOnComplete === true) {
        try {
          windowRef.focus();
        } catch {
          // ignore focus failures
        }
      }
      if (typeof options?.onComplete === 'function') {
        try {
          options.onComplete({
            windowRef,
            targetBounds
          });
        } catch {
          // ignore animation completion hook failures
        }
      }
      broadcastMessengerWindowShellState();
    }, Math.max(220, durationMs));
    return;
  }

  try {
    if (usePositionOnly) {
      windowRef.setPosition(startBounds.x, startBounds.y, false);
    } else {
      windowRef.setBounds(startBounds, false);
    }
  } catch {
    // ignore initial animation frame failures
  }

  const finalize = () => {
    messengerWindowHideTimer = 0;
    messengerWindowAnimationDirection = '';
    try {
      if (usePositionOnly) {
        windowRef.setPosition(targetBounds.x, targetBounds.y, false);
      } else {
        windowRef.setBounds(targetBounds, false);
      }
    } catch {
      // ignore final bounds failures
    }
    if (options?.hideAfter === true) {
      try {
        windowRef.hide();
      } catch {
        // ignore hide failures
      }
    }
    if (options?.focusOnComplete === true) {
      try {
        windowRef.focus();
      } catch {
        // ignore focus failures
      }
    }
    if (typeof options?.onComplete === 'function') {
      try {
        options.onComplete({
          windowRef,
          targetBounds
        });
      } catch {
        // ignore animation completion hook failures
      }
    }
    broadcastMessengerWindowShellState();
  };

  const step = () => {
    if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
      messengerWindowHideTimer = 0;
      messengerWindowAnimationDirection = '';
      return;
    }
    const now = typeof performance?.now === 'function' ? performance.now() : Date.now();
    const elapsed = now - startedAt;
    const rawProgress = durationMs > 0 ? Math.min(1, elapsed / durationMs) : 1;
    const easedProgress = resolveMessengerAnimationProgress(rawProgress, messengerWindowAnimationDirection);
    const nextBounds = interpolateBounds(startBounds, targetBounds, easedProgress);
    try {
      if (usePositionOnly) {
        windowRef.setPosition(nextBounds.x, nextBounds.y, false);
      } else {
        windowRef.setBounds(nextBounds, false);
      }
    } catch {
      // ignore animation frame failures
    }
    if (rawProgress >= 1) {
      finalize();
      return;
    }
    messengerWindowHideTimer = setTimeout(step, MESSENGER_WINDOW_ANIMATION_FRAME_MS);
  };

  const startManualAnimation = () => {
    if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
      messengerWindowHideTimer = 0;
      messengerWindowAnimationDirection = '';
      return;
    }
    startedAt = typeof performance?.now === 'function' ? performance.now() : Date.now();
    step();
  };

  if (startDelayMs > 0) {
    messengerWindowHideTimer = setTimeout(startManualAnimation, startDelayMs);
    return;
  }

  startManualAnimation();
}

function revealMessengerWindowNow(windowRef, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
    return {
      ok: false,
      reason: 'window-unavailable',
      state: getMessengerWindowShellState()
    };
  }

  clearMessengerWindowHideTimer();
  const animate = options?.animate !== false;
  const focus = options?.focus !== false;
  const anchorBounds = options?.sourceBounds || mainWindowNormalBounds || windowRef.getBounds();
  const hiddenBounds = buildHiddenMessengerWindowBounds(anchorBounds);
  const visibleBounds = buildMessengerWindowBounds(anchorBounds);
  const wasVisible = windowRef.isVisible();
  const currentBounds = normalizePersistedWindowBounds(windowRef.getBounds(), {
    minWidth: 320,
    minHeight: 240
  });
  const shouldStartFromHidden = messengerWindowIsHidden === true || !wasVisible;

  applyMessengerWindowPresentation(windowRef, {
    sourceBounds: anchorBounds,
    animate: false,
    placement: false,
    show: false,
    preserveCurrentWindowShape: false
  });
  try {
    if (windowRef.isMinimized()) {
      windowRef.restore();
    }
  } catch {
    // ignore restore failures
  }
  if (shouldStartFromHidden) {
    try {
      windowRef.setBounds(hiddenBounds, false);
    } catch {
      // ignore pre-show placement failures
    }
  }
  if (!windowRef.isVisible()) {
    if (focus === false && typeof windowRef.showInactive === 'function') {
      windowRef.showInactive();
    } else {
      windowRef.show();
    }
  }
  try {
    windowRef.moveTop();
  } catch {
    // ignore move-to-top failures
  }
  messengerWindowIsHidden = false;
  if (animate) {
    animateMessengerWindowBounds(
      windowRef,
      shouldStartFromHidden ? hiddenBounds : (currentBounds || hiddenBounds),
      visibleBounds,
      {
        direction: 'show',
        useNativeAnimation: false,
        startDelayMs: shouldStartFromHidden ? MESSENGER_WINDOW_ANIMATION_FRAME_MS : 0,
        focusOnComplete: focus,
        onComplete: () => {
          messengerWindowExpandedBounds = normalizePersistedWindowBounds(visibleBounds, {
            minWidth: 1,
            minHeight: 1
          });
          messengerWindowIsHidden = false;
        }
      }
    );
  } else {
    try {
      windowRef.setBounds(visibleBounds, false);
    } catch {
      // ignore reveal placement failures
    }
    if (focus) {
      windowRef.focus();
    }
  }
  messengerWindowExpandedBounds = normalizePersistedWindowBounds(visibleBounds, {
    minWidth: 1,
    minHeight: 1
  });
  messengerWindowIsHidden = false;
  broadcastMessengerWindowShellState();
  return {
    ok: true,
    reason: '',
    state: getMessengerWindowShellState()
  };
}

function showMessengerWindow(options = {}) {
  return revealMessengerWindowNow(mainWindow, options);
}

function hideMessengerWindow(options = {}) {
  clearMessengerWindowHideTimer();

  const windowRef = mainWindow;
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
    broadcastMessengerWindowShellState();
    return {
      ok: true,
      reason: '',
      state: getMessengerWindowShellState()
    };
  }

  const animate = options?.animate === true;
  const focusMain = options?.focusMain !== false;
  const anchorBounds = options?.sourceBounds || mainWindowNormalBounds || windowRef.getBounds();
  const preserveCurrentWindowShape = options?.preserveCurrentWindowShape === true;
  const visibleBounds = buildMessengerWindowBounds(anchorBounds);
  const currentBounds = normalizePersistedWindowBounds(windowRef.getBounds(), {
    minWidth: 1,
    minHeight: 1
  }) || visibleBounds;
  const hiddenBounds = buildHiddenMessengerWindowBounds(anchorBounds);
  const fullyHiddenCurrentBounds = buildFullyHiddenWindowBounds(currentBounds) || hiddenBounds;
  messengerWindowExpandedBounds = normalizePersistedWindowBounds(currentBounds, {
    minWidth: 1,
    minHeight: 1
  });

  if (preserveCurrentWindowShape) {
    detachWindowForFreeformAnimation(windowRef, currentBounds);
  }

  applyMessengerWindowPresentation(windowRef, {
    sourceBounds: anchorBounds,
    animate: false,
    placement: false,
    show: false,
    preserveCurrentWindowShape
  });

  if (!windowRef.isVisible()) {
    try {
      windowRef.setBounds(hiddenBounds, false);
    } catch {
      // ignore hide placement failures
    }
    messengerWindowIsHidden = true;
    try {
      windowRef.blur();
    } catch {
      // ignore blur failures
    }
    broadcastMessengerWindowShellState();
    return {
      ok: true,
      reason: '',
      state: getMessengerWindowShellState()
    };
  }

  if (animate) {
    animateMessengerWindowBounds(
      windowRef,
      currentBounds,
      preserveCurrentWindowShape ? fullyHiddenCurrentBounds : hiddenBounds,
      {
        direction: 'hide',
        useNativeAnimation: false,
        onComplete: () => {
          try {
            windowRef.setBounds(hiddenBounds, false);
          } catch {
            // ignore hidden messenger placement failures
          }
          messengerWindowIsHidden = true;
          try {
            windowRef.blur();
          } catch {
            // ignore blur failures
          }
        }
      }
    );
  } else {
    try {
      windowRef.setBounds(hiddenBounds, false);
    } catch {
      // ignore hide placement failures
    }
    messengerWindowIsHidden = true;
    try {
      windowRef.blur();
    } catch {
      // ignore blur failures
    }
  }

  if (focusMain && mainWindow instanceof BrowserWindow && !mainWindow.isDestroyed()) {
    try {
      if (mainWindow.isVisible() && messengerWindowIsHidden !== true) {
        mainWindow.focus();
      }
    } catch {
      // ignore focus failures
    }
  }

  broadcastMessengerWindowShellState();
  return {
    ok: true,
    reason: '',
    state: getMessengerWindowShellState()
  };
}

function refreshMessengerWindowShortcutRegistration() {
  if (registeredMessengerWindowShortcut) {
    try {
      globalShortcut.unregister(registeredMessengerWindowShortcut);
    } catch {
      // ignore unregister failures
    }
    registeredMessengerWindowShortcut = '';
  }

  if (!app.isReady() || normalizeWindowMode(messengerWindowMode) !== WINDOW_MODE_MESSENGER) {
    return {
      ok: true,
      disabled: true,
      reason: '',
      state: getMessengerWindowShellState()
    };
  }

  const normalizedShortcut = normalizeKeyboardShortcut(messengerWindowShortcut || DEFAULT_MESSENGER_SHORTCUT) || DEFAULT_MESSENGER_SHORTCUT;
  const accelerator = shortcutTokenToAccelerator(normalizedShortcut);
  if (!accelerator) {
    return {
      ok: false,
      disabled: false,
      reason: 'shortcut-invalid',
      state: getMessengerWindowShellState()
    };
  }

  try {
    const registered = globalShortcut.register(accelerator, () => {
      if (normalizeWindowMode(messengerWindowMode) !== WINDOW_MODE_MESSENGER) return;
      if (!(mainWindow instanceof BrowserWindow) || mainWindow.isDestroyed()) return;
      const activeDirection = messengerWindowAnimationDirection;
      clearMessengerWindowHideTimer({ preserveDirection: true });
      if (activeDirection === 'hide') {
        revealMessengerWindowNow(mainWindow, {
          animate: true,
          focus: true
        });
        return;
      }
      if (activeDirection === 'show') {
        hideMessengerWindow({
          animate: true,
          focusMain: false
        });
        return;
      }
      if (messengerWindowIsHidden === true || !mainWindow.isVisible()) {
        revealMessengerWindowNow(mainWindow, {
          animate: true,
          focus: true
        });
        return;
      }
      hideMessengerWindow({
        animate: true,
        focusMain: false
      });
    });
    if (!registered) {
      return {
        ok: false,
        disabled: false,
        reason: 'shortcut-unavailable',
        state: getMessengerWindowShellState()
      };
    }
    registeredMessengerWindowShortcut = accelerator;
    broadcastMessengerWindowShellState();
    return {
      ok: true,
      disabled: false,
      reason: '',
      state: getMessengerWindowShellState()
    };
  } catch {
    return {
      ok: false,
      disabled: false,
      reason: 'shortcut-unavailable',
      state: getMessengerWindowShellState()
    };
  }
}

function activateMessengerWindowMode(options = {}) {
  if (!(mainWindow instanceof BrowserWindow) || mainWindow.isDestroyed()) {
    return {
      ok: false,
      reason: 'window-unavailable',
      state: getMessengerWindowShellState()
    };
  }

  if (options.preserveNormalState !== false) {
    captureMainWindowNormalState(mainWindow);
  }

  clearMessengerWindowHideTimer();
  const anchorBounds = mainWindowNormalBounds || mainWindow.getBounds();
  const currentBounds = normalizePersistedWindowBounds(mainWindow.getBounds(), {
    minWidth: 320,
    minHeight: 240
  }) || normalizePersistedWindowBounds(anchorBounds, {
    minWidth: 320,
    minHeight: 240
  });
  messengerWindowMode = WINDOW_MODE_MESSENGER;
  messengerWindowIsHidden = false;
  messengerWindowExpandedBounds = normalizePersistedWindowBounds(currentBounds, {
    minWidth: 1,
    minHeight: 1
  });
  applyMainWindowMinimumSize(mainWindow, { messengerMode: true });
  applyMessengerWindowPresentation(mainWindow, {
    sourceBounds: anchorBounds,
    animate: false,
    placement: options.hideAfterActivate === true ? false : 'visible',
    show: options.hideAfterActivate === true ? false : options.show !== false,
    focus: options.focus !== false,
    preserveCurrentWindowShape: options.hideAfterActivate === true
  });

  const shortcutResult = refreshMessengerWindowShortcutRegistration();
  if (shortcutResult.ok !== true && shortcutResult.disabled !== true) {
    messengerWindowMode = WINDOW_MODE_NORMAL;
    messengerWindowIsHidden = false;
    try {
      mainWindow.setAlwaysOnTop(false);
    } catch {
      // ignore always-on-top restore failures
    }
    try {
      mainWindow.setVisibleOnAllWorkspaces(false);
    } catch {
      // ignore workspace visibility restore failures
    }
    persistMainWindowState(mainWindow, { force: true });
    broadcastMessengerWindowShellState();
    return {
      ok: false,
      reason: shortcutResult.reason || 'shortcut-unavailable',
      state: getMessengerWindowShellState()
    };
  }
  persistMainWindowState(mainWindow, { force: true });
  broadcastMessengerWindowShellState();
  if (options.hideAfterActivate === true) {
    if (currentBounds) {
      try {
        mainWindow.setBounds(currentBounds, false);
      } catch {
        // ignore current bounds restoration failures
      }
    }
    if (!mainWindow.isVisible()) {
      mainWindow.show();
    }
    hideMessengerWindow({
      animate: options.animate === true,
      focusMain: false,
      sourceBounds: anchorBounds,
      preserveCurrentWindowShape: true
    });
  }
  return {
    ok: true,
    reason: shortcutResult.ok || shortcutResult.disabled === true ? '' : shortcutResult.reason,
    state: getMessengerWindowShellState()
  };
}

function restoreMessengerWindowMode(options = {}) {
  if (!(mainWindow instanceof BrowserWindow) || mainWindow.isDestroyed()) {
    return {
      ok: false,
      reason: 'window-unavailable',
      state: getMessengerWindowShellState()
    };
  }

  clearMessengerWindowHideTimer();
  messengerWindowMode = WINDOW_MODE_NORMAL;
  messengerWindowIsHidden = false;
  messengerWindowExpandedBounds = null;
  applyMainWindowMinimumSize(mainWindow, { messengerMode: false });
  const targetBounds = normalizePersistedWindowBounds(mainWindowNormalBounds, {
    minWidth: MAIN_WINDOW_MIN_WIDTH,
    minHeight: MAIN_WINDOW_MIN_HEIGHT
  });

  try {
    mainWindow.setAlwaysOnTop(false);
  } catch {
    // ignore always-on-top failures
  }
  try {
    if (mainWindow.isFullScreen()) {
      mainWindow.setFullScreen(false);
    }
  } catch {
    // ignore fullscreen transition failures
  }
  try {
    mainWindow.setFullScreenable(true);
  } catch {
    // ignore fullscreenable restore failures
  }
  try {
    mainWindow.setVisibleOnAllWorkspaces(false);
  } catch {
    // ignore workspace visibility restore failures
  }
  try {
    if (mainWindow.isMaximized()) {
      mainWindow.unmaximize();
    }
  } catch {
    // ignore maximize reset failures
  }
  if (targetBounds) {
    try {
      mainWindow.setBounds(targetBounds, options.animate === true);
    } catch {
      // ignore restore bounds failures
    }
  }
  if (mainWindowNormalIsMaximized === true) {
    try {
      if (!mainWindow.isMaximized()) {
        mainWindow.maximize();
      }
    } catch {
      // ignore maximize restore failures
    }
  }
  applyMessengerWindowOpacity(mainWindow);
  if (options.show !== false) {
    if (!mainWindow.isVisible()) {
      mainWindow.show();
    }
    mainWindow.focus();
  }

  refreshMessengerWindowShortcutRegistration();
  persistMainWindowState(mainWindow, { force: true });
  broadcastMessengerWindowShellState();
  return {
    ok: true,
    reason: '',
    state: getMessengerWindowShellState()
  };
}

function toggleMessengerWindowMode(options = {}) {
  return normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER
    ? restoreMessengerWindowMode(options)
    : activateMessengerWindowMode(options);
}

function readCliArgValue(flagName) {
  const flagIndex = process.argv.indexOf(flagName);
  if (flagIndex >= 0) {
    const nextValue = process.argv[flagIndex + 1];
    return typeof nextValue === 'string' && !nextValue.startsWith('--') ? nextValue : '';
  }

  const matchingArg = process.argv.find((arg) => arg.startsWith(`${flagName}=`));
  if (!matchingArg) {
    return '';
  }

  return matchingArg.slice(flagName.length + 1);
}

const isSmokeTest = SMOKE_TEST_REQUESTED;
const ENABLE_DIAGNOSTICS_CAPTURE = (
  process.argv.includes('--capture-diagnostics')
  || process.env.YUCHAT_CAPTURE_DIAGNOSTICS === '1'
);
const ENABLE_MAIN_WS_DEBUG_BRIDGE = !(
  process.argv.includes('--disable-main-ws-debug-bridge')
  || process.env.YUCHAT_DISABLE_MAIN_WS_DEBUG_BRIDGE === '1'
);
const ENABLE_PROD_DEVTOOLS_AUTO_OPEN = (
  process.argv.includes('--enable-prod-devtools-auto-open')
  || process.env.YUCHAT_ENABLE_PROD_DEVTOOLS_AUTO_OPEN === '1'
);
const ENABLE_RUNTIME_LOGS = (
  process.argv.includes('--enable-runtime-logs')
  || process.env.YUCHAT_ENABLE_RUNTIME_LOGS === '1'
);
const ENABLE_PREBOOT_ERROR_BANNERS = (
  process.argv.includes('--enable-preboot-error-banners')
  || process.env.YUCHAT_ENABLE_PREBOOT_ERROR_BANNERS === '1'
);
const ENABLE_DEVTOOLS_AUTO_OPEN = (
  (!app.isPackaged || ENABLE_PROD_DEVTOOLS_AUTO_OPEN)
  && (
    process.argv.includes('--open-devtools')
    || process.env.YUCHAT_ENABLE_DEVTOOLS_AUTO_OPEN === '1'
    || process.env.YUCHAT_ENABLE_PROD_DEVTOOLS_AUTO_OPEN === '1'
  )
);
const DIAGNOSTICS_MAX_CONSOLE_ENTRIES = Math.max(
  200,
  Number(readCliArgValue('--diag-console-limit')) || 1200
);
const DIAGNOSTICS_MAX_NETWORK_ENTRIES = Math.max(
  200,
  Number(readCliArgValue('--diag-network-limit')) || 3000
);
const diagnosticsArtifactsDir = path.resolve(
  readCliArgValue('--diag-output-dir') || path.join(__dirname, 'artifacts', 'diagnostics')
);
const diagnosticsSummaryPath = path.join(diagnosticsArtifactsDir, 'latest-summary.json');
const diagnosticsConsolePath = path.join(diagnosticsArtifactsDir, 'latest-console.jsonl');
const diagnosticsHarPath = path.join(diagnosticsArtifactsDir, 'latest-network.har.json');
const diagnosticsRawNetworkPath = path.join(diagnosticsArtifactsDir, 'latest-network-raw.json');
const SMOKE_TEST_TIMEOUT_MS = Math.max(15000, Number(readCliArgValue('--smoke-timeout')) || 60000);
const YUCHAT_ENTRY_URL = String(readCliArgValue('--yuchat-url') || 'https://yuchat.rt.ru').trim() || 'https://yuchat.rt.ru';
const smokeArtifactsDir = path.resolve(
  readCliArgValue('--smoke-output-dir') || path.join(__dirname, 'artifacts', 'smoke')
);
const smokeReportPath = path.join(smokeArtifactsDir, 'latest-report.json');
const smokeScreenshotPath = path.join(smokeArtifactsDir, 'latest-window.png');
const smokeLogPath = path.join(smokeArtifactsDir, 'latest-log.txt');
const smokeTestState = isSmokeTest
  ? {
      startedAt: new Date().toISOString(),
      completedAt: '',
      ok: false,
      summary: '',
      platform: process.platform,
      arch: process.arch,
      electronVersion: process.versions.electron,
      chromeVersion: process.versions.chrome,
      nodeVersion: process.versions.node,
      shell: {
        loaded: false,
        snapshot: null
      },
      view: {
        created: false,
        targetUrl: YUCHAT_ENTRY_URL,
        currentUrl: '',
        didStartLoading: false,
        domReady: false,
        didFinishLoad: false,
        lastFailLoad: null,
        snapshot: null,
        preloadHeartbeat: null
      },
      failures: [],
      events: [],
      artifacts: {
        reportPath: smokeReportPath,
        screenshotPath: ''
      }
    }
  : null;
let smokeFinalizeInFlight = null;
let smokeTimeoutHandle = 0;
let smokeEvaluationTimer = 0;
const preloadRecoveryAttemptedByContentsId = new Set();
const preloadHeartbeatsByWebContentsId = new Map();
let voskRuntimeReadyPromise = null;
const diagnosticCaptureSessions = new WeakSet();
const diagnosticCaptureWebContents = new WeakSet();
const diagnosticPendingRequestsById = new Map();
const diagnosticNetworkEntries = [];
const diagnosticConsoleEntries = [];
const activeTransferAbortHandlersById = new Map();
let diagnosticFlushTimer = 0;
const diagnosticsState = ENABLE_DIAGNOSTICS_CAPTURE
  ? {
      startedAt: new Date().toISOString(),
      flushCount: 0
    }
  : null;

function runtimeWarn(...args) {
  if (!ENABLE_RUNTIME_LOGS) return;
  console.warn(...args);
}

function runtimeInfo(...args) {
  if (!ENABLE_RUNTIME_LOGS) return;
  console.info(...args);
}

if (LEGACY_PRELOAD_REQUESTED && !LEGACY_PRELOAD_AVAILABLE) {
  console.warn('[YuChat] Legacy preload requested, but highlightPreload.js is missing. Falling back to fullCustomPreload.js');
}

try {
  app.setName(YUCHAT_STORAGE_NAME);
} catch {
  // ignore app name setup issues in dev
}

try {
  const stableUserDataPath = path.join(app.getPath('appData'), YUCHAT_STORAGE_PROFILE_NAME);
  app.setPath('userData', stableUserDataPath);
  app.setPath('sessionData', path.join(stableUserDataPath, 'session'));
} catch (error) {
  runtimeWarn('[YuChat] Failed to pin storage paths:', error);
}

const hasSingleInstanceLock = (() => {
  if (!SHOULD_ENFORCE_SINGLE_INSTANCE) {
    return true;
  }
  if (isSmokeTest) {
    return true;
  }
  try {
    return app.requestSingleInstanceLock();
  } catch (error) {
    runtimeWarn('[YuChat] Failed to request single-instance lock:', error);
    return true;
  }
})();

if (!hasSingleInstanceLock) {
  app.exit(0);
}

function ensureDirSync(targetDir) {
  fs.mkdirSync(targetDir, { recursive: true });
}

function getVoskRuntimeBaseDir() {
  const override = String(process.env.YUCHAT_VOSK_RUNTIME_DIR || '').trim();
  if (override) {
    return path.resolve(override);
  }
  const devRuntimeDir = path.join(__dirname, '.runtime', 'vosk-dictation');
  if (app && app.isPackaged === false) {
    return devRuntimeDir;
  }
  try {
    return path.join(app.getPath('userData'), 'vosk-dictation');
  } catch {
    return devRuntimeDir;
  }
}

function getVoskPackagesDir() {
  return path.join(getVoskRuntimeBaseDir(), 'python-packages');
}

function getVoskModelsDir() {
  return path.join(getVoskRuntimeBaseDir(), 'models');
}

function getVoskModelDir() {
  return path.join(getVoskModelsDir(), VOSK_MODEL_NAME);
}

function getVoskHelperRuntimePath() {
  return path.join(getVoskRuntimeBaseDir(), 'runtime', VOSK_HELPER_FILE_NAME);
}

function getVoskPythonBinary() {
  return String(process.env.YUCHAT_VOSK_PYTHON || 'python3').trim() || 'python3';
}

function parseJsonLine(text = '') {
  const normalized = String(text || '').trim();
  if (!normalized) return null;
  try {
    return JSON.parse(normalized);
  } catch {
    return null;
  }
}

function runChildProcess(command = '', args = [], options = {}) {
  return new Promise((resolve, reject) => {
    let settled = false;
    const child = spawn(command, args, {
      cwd: options.cwd || __dirname,
      env: {
        ...process.env,
        ...(options.env || {})
      },
      stdio: ['ignore', 'pipe', 'pipe']
    });
    let stdout = '';
    let stderr = '';
    let stdoutLineBuffer = '';
    let stderrLineBuffer = '';
    const emitBufferedLines = (kind = 'stdout', flush = false) => {
      const isStdout = kind === 'stdout';
      let buffer = isStdout ? stdoutLineBuffer : stderrLineBuffer;
      const handler = isStdout ? options.onStdoutLine : options.onStderrLine;
      if (typeof handler !== 'function' || !buffer) {
        if (isStdout) {
          stdoutLineBuffer = buffer;
        } else {
          stderrLineBuffer = buffer;
        }
        return;
      }
      const lines = buffer.split(/\r?\n/u);
      buffer = flush ? '' : String(lines.pop() || '');
      lines.forEach((line) => {
        const normalizedLine = String(line || '').trim();
        if (!normalizedLine) return;
        try {
          handler(normalizedLine);
        } catch {
          // ignore progress callback failures
        }
      });
      if (isStdout) {
        stdoutLineBuffer = buffer;
      } else {
        stderrLineBuffer = buffer;
      }
    };
    child.stdout.on('data', (chunk) => {
      const text = String(chunk || '');
      stdout += text;
      stdoutLineBuffer += text;
      emitBufferedLines('stdout', false);
    });
    child.stderr.on('data', (chunk) => {
      const text = String(chunk || '');
      stderr += text;
      stderrLineBuffer += text;
      emitBufferedLines('stderr', false);
    });
    const abortSignal = options.signal;
    const handleAbort = () => {
      if (settled) return;
      settled = true;
      const abortError = abortSignal?.reason instanceof Error
        ? abortSignal.reason
        : createTransferAbortError(abortSignal?.reason || 'canceled');
      try {
        child.kill('SIGTERM');
      } catch {
        // ignore kill failures during abort
      }
      reject(abortError);
    };
    if (abortSignal && typeof abortSignal.addEventListener === 'function') {
      if (abortSignal.aborted) {
        handleAbort();
        return;
      }
      abortSignal.addEventListener('abort', handleAbort, { once: true });
    }
    child.on('error', (error) => {
      if (settled) return;
      settled = true;
      if (abortSignal && typeof abortSignal.removeEventListener === 'function') {
        abortSignal.removeEventListener('abort', handleAbort);
      }
      if (String(error?.code || '').trim().toUpperCase() === 'ENOENT') {
        reject(new Error(`Не найден исполняемый файл ${command}. Установите Python 3 и повторите.`));
        return;
      }
      reject(error);
    });
    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      if (abortSignal && typeof abortSignal.removeEventListener === 'function') {
        abortSignal.removeEventListener('abort', handleAbort);
      }
      emitBufferedLines('stdout', true);
      emitBufferedLines('stderr', true);
      if (code === 0) {
        resolve({ stdout, stderr, code });
        return;
      }
      const error = new Error((stderr || stdout || `Command failed: ${command}`).trim());
      error.code = code;
      error.stdout = stdout;
      error.stderr = stderr;
      reject(error);
    });
  });
}

function ensureVoskHelperRuntimeFile() {
  ensureDirSync(path.dirname(getVoskHelperRuntimePath()));
  const source = fs.readFileSync(VOSK_HELPER_SOURCE_PATH, 'utf8');
  const runtimePath = getVoskHelperRuntimePath();
  const current = fs.existsSync(runtimePath)
    ? fs.readFileSync(runtimePath, 'utf8')
    : '';
  if (current !== source) {
    fs.writeFileSync(runtimePath, source, 'utf8');
  }
  return runtimePath;
}

async function canUseSystemVoskPythonPackages() {
  try {
    await runChildProcess(getVoskPythonBinary(), [
      '-c',
      'import vosk, cffi, pycparser'
    ], {
      env: {
        PYTHONNOUSERSITE: '1'
      }
    });
    return true;
  } catch {
    return false;
  }
}

function writeTextFileIfChanged(filePath = '', content = '') {
  const targetPath = String(filePath || '').trim();
  if (!targetPath) return;
  ensureDirSync(path.dirname(targetPath));
  const current = fs.existsSync(targetPath)
    ? fs.readFileSync(targetPath, 'utf8')
    : '';
  if (current !== content) {
    fs.writeFileSync(targetPath, content, 'utf8');
  }
}

function removePathSync(targetPath = '') {
  const resolvedPath = String(targetPath || '').trim();
  if (!resolvedPath || !fs.existsSync(resolvedPath)) return;
  try {
    fs.rmSync(resolvedPath, {
      recursive: true,
      force: true
    });
  } catch (error) {
    if (error?.code !== 'ENOENT') {
      throw error;
    }
  }
}

function ensureVoskStubModules(packagesDir = '') {
  const targetDir = String(packagesDir || '').trim();
  if (!targetDir) return;
  writeTextFileIfChanged(path.join(targetDir, 'requests.py'), VOSK_STUB_REQUESTS_SOURCE);
  writeTextFileIfChanged(path.join(targetDir, 'srt.py'), VOSK_STUB_SRT_SOURCE);
  writeTextFileIfChanged(path.join(targetDir, 'tqdm.py'), VOSK_STUB_TQDM_SOURCE);
}

function createVoskTimeoutError(message = '') {
  const error = new Error(String(message || 'Истекло время ожидания подготовки Vosk.'));
  error.code = 'ETIMEDOUT';
  return error;
}

function resolveVoskAbortError(error, controller = null, fallbackMessage = '') {
  if (controller?.signal?.aborted) {
    const reason = controller.signal.reason;
    if (reason instanceof Error) {
      return reason;
    }
    return createVoskTimeoutError(fallbackMessage || String(reason || 'Подготовка Vosk была прервана.'));
  }
  return error;
}

function startAbortTimer(controller = null, timeoutMs = 0, message = '') {
  if (!controller || !(Number(timeoutMs) > 0)) {
    return () => {};
  }
  const timer = setTimeout(() => {
    if (!controller.signal.aborted) {
      controller.abort(createVoskTimeoutError(message));
    }
  }, Math.max(1, Number(timeoutMs) || 0));
  return () => clearTimeout(timer);
}

function getUsableFetchSession(preferredSession = null) {
  if (preferredSession && typeof preferredSession.fetch === 'function') {
    return preferredSession;
  }
  if (session?.defaultSession && typeof session.defaultSession.fetch === 'function') {
    return session.defaultSession;
  }
  return null;
}

function getPreferredFetchSession(event = null) {
  return getUsableFetchSession(event?.sender?.session || null);
}

async function fetchWithResolvedSession(fetchSession = null, url = '', options = {}) {
  const resolvedSession = getUsableFetchSession(fetchSession);
  if (!resolvedSession) {
    throw new Error('Сессия загрузки недоступна.');
  }
  const timeoutMs = Math.max(0, Number(options.timeoutMs) || 0);
  const timeoutMessage = trimText(
    options.timeoutMessage || `Не удалось дождаться ответа сервера Vosk за ${Math.ceil(timeoutMs / 1000)} сек.`,
    220
  );
  const controller = !options.signal && timeoutMs > 0 && typeof AbortController === 'function'
    ? new AbortController()
    : null;
  const clearTimeoutHandle = startAbortTimer(
    controller,
    timeoutMs,
    timeoutMessage
  );
  try {
    return await resolvedSession.fetch(String(url || '').trim(), {
      method: options.method || 'GET',
      cache: 'no-store',
      headers: {
        ...(options.headers || {})
      },
      body: options.body,
      redirect: options.redirect,
      signal: options.signal || controller?.signal
    });
  } catch (error) {
    throw resolveVoskAbortError(
      error,
      controller,
      timeoutMessage
    );
  } finally {
    clearTimeoutHandle();
  }
}

async function fetchWithPreferredSession(event = null, url = '', options = {}) {
  return fetchWithResolvedSession(getPreferredFetchSession(event), url, options);
}

async function fetchJsonWithPreferredSession(event = null, url = '') {
  const response = await fetchWithPreferredSession(event, url, {
    timeoutMs: VOSK_METADATA_FETCH_TIMEOUT_MS,
    headers: {
      Accept: 'application/json'
    }
  });
  if (!response.ok) {
    throw new Error(`Не удалось получить метаданные ${url} (${response.status}).`);
  }
  return response.json();
}

function normalizeCorporatePortalFetchUrl(value = '') {
  const raw = String(value || '').trim();
  if (!raw) return '';
  try {
    const parsed = new URL(raw);
    if (parsed.protocol !== 'https:') return '';
    if (!CORPORATE_PORTAL_ALLOWED_ORIGINS.has(parsed.origin)) return '';
    parsed.username = '';
    parsed.password = '';
    return parsed.toString();
  } catch {
    return '';
  }
}

function isAllowedTrueconfHostname(hostname = '') {
  const normalized = String(hostname || '').trim().toLowerCase();
  return Boolean(normalized) && normalized.length <= 253 && !/[\s/@\\]/u.test(normalized);
}

function normalizeTrueconfBaseUrl(value = '') {
  const raw = String(value || '').trim();
  if (!raw) return '';
  const candidate = raw.includes('://') ? raw : `https://${raw}`;
  try {
    const parsed = new URL(candidate);
    if (!['http:', 'https:'].includes(parsed.protocol)) return '';
    if (!isAllowedTrueconfHostname(parsed.hostname)) return '';
    parsed.username = '';
    parsed.password = '';
    parsed.pathname = '/';
    parsed.search = '';
    parsed.hash = '';
    return parsed.toString().replace(/\/$/, '');
  } catch {
    return '';
  }
}

function buildTrueconfRoomPublicUrl(baseUrl = '', roomId = '') {
  const normalizedBase = normalizeTrueconfBaseUrl(baseUrl);
  const normalizedRoomId = pickFirstTrueconfString(roomId || '', 180);
  if (!normalizedBase || !normalizedRoomId) return '';
  try {
    return `${normalizedBase}/c/${encodeURIComponent(normalizedRoomId)}`;
  } catch {
    return '';
  }
}

function normalizeTrueconfApiUrl(baseUrl = '', endpoint = '') {
  const normalizedBase = normalizeTrueconfBaseUrl(baseUrl);
  const rawEndpoint = String(endpoint || '').trim();
  if (!normalizedBase || !rawEndpoint) return '';
  try {
    const resolved = new URL(rawEndpoint, `${normalizedBase}/`);
    if (resolved.protocol !== 'https:') return '';
    if (!isAllowedTrueconfHostname(resolved.hostname)) return '';
    if (!String(resolved.pathname || '').startsWith('/api/')) return '';
    resolved.username = '';
    resolved.password = '';
    resolved.hash = '';
    return resolved.toString();
  } catch {
    return '';
  }
}

function buildTrueconfRequestHeaders() {
  return {
    Accept: 'application/json, text/plain, */*'
  };
}

function pickFirstTrueconfString(values = [], maxLength = 240) {
  const candidateList = Array.isArray(values) ? values : [values];
  for (const value of candidateList) {
    const normalized = trimText(value || '', maxLength).trim();
    if (normalized) {
      return normalized;
    }
  }
  return '';
}

function normalizeTrueconfRoomRecord(record = null, options = {}) {
  if (!isPlainRecord(record)) return null;
  const roomId = pickFirstTrueconfString([
    record.id,
    record.conference_id,
    record.conferenceId,
    record.meeting_id,
    record.meetingId,
    record.uid
  ], 180);
  if (!roomId) return null;
  const topic = pickFirstTrueconfString([
    record.topic,
    record.name,
    record.title,
    record.display_name,
    record.displayName
  ], 240) || roomId;
  const joinUrl = pickFirstTrueconfString([
    record.join_url,
    record.joinUrl,
    record.web_url,
    record.webUrl,
    record.invite_url,
    record.inviteUrl,
    record.url
  ], 2048);
  return {
    id: roomId,
    title: topic,
    joinUrl,
    sourceType: pickFirstTrueconfString(options.sourceType || '', 40) || 'unknown',
    state: pickFirstTrueconfString(record.state || '', 40),
    owner: pickFirstTrueconfString(record.owner || record.owner_id || '', 240),
    access: pickFirstTrueconfString(record.access || '', 40)
  };
}

function collectTrueconfRoomRecords(response = null, sourceType = 'unknown') {
  const input = isPlainRecord(response) ? response : {};
  const rawList = Array.isArray(input.list)
    ? input.list
    : (Array.isArray(input.conferences) ? input.conferences : []);
  return rawList
    .map((entry) => normalizeTrueconfRoomRecord(entry, { sourceType }))
    .filter(Boolean);
}

function buildTrueconfListPath(payload = {}) {
  const timezone = trimText(payload?.timezone || 'Europe/Moscow', 80).trim() || 'Europe/Moscow';
  const requestedPageSize = Math.max(1, Math.min(TRUECONF_MAX_LIST_PAGE_SIZE, Number(payload?.pageSize || 120) || 120));
  const params = new URLSearchParams();
  params.set('page', '1');
  params.set('page_size', String(requestedPageSize));
  params.set('url_type', 'fixed');
  params.set('sort_field', 'topic');
  params.set('sort_order', '0');
  params.set('timezone', timezone);
  params.set('invitations_substring', 'true');
  params.append('schedule_type[]', 'none');
  return `/api/v4/conferences?${params.toString()}`;
}

async function requestTrueconfJson(event = null, payload = {}, endpoint = '', options = {}) {
  const baseUrl = normalizeTrueconfBaseUrl(payload?.baseUrl || payload?.url || '');
  if (!baseUrl) {
    const error = new Error('Укажите корректный адрес TrueConf в формате https://<сервер>.trueconf.rt.ru.');
    error.code = 'TRUECONF_URL_INVALID';
    throw error;
  }
  const requestUrl = normalizeTrueconfApiUrl(baseUrl, endpoint);
  if (!requestUrl) {
    const error = new Error('Не удалось подготовить URL запроса TrueConf.');
    error.code = 'TRUECONF_URL_INVALID';
    throw error;
  }
  const targetSession = getPreferredFetchSession(event) || getPersistentYuchatSession();
  const timeoutMs = Math.max(1000, Math.min(45000, Number(options?.timeoutMs || TRUECONF_DEFAULT_TIMEOUT_MS) || TRUECONF_DEFAULT_TIMEOUT_MS));
  const response = await fetchWithResolvedSession(targetSession, requestUrl, {
    method: 'GET',
    timeoutMs,
    timeoutMessage: `Не удалось дождаться ответа TrueConf за ${Math.ceil(timeoutMs / 1000)} сек.`,
    headers: buildTrueconfRequestHeaders(),
    redirect: 'follow'
  });
  const { rawText, parsed } = await readJsonResponse(response);
  if (!response.ok) {
    const authRequired = [401, 403].includes(Number(response.status || 0));
    const responseErrorText = (
      pickFirstTrueconfString(parsed?.error?.message || '', 180)
      || pickFirstTrueconfString(parsed?.message || '', 180)
    );
    const error = new Error(
      authRequired
        ? 'TrueConf требует авторизацию. Выполните вход в веб-окне TrueConf.'
        : (responseErrorText || `TrueConf вернул ${response.status}.`)
    );
    error.code = authRequired ? 'TRUECONF_AUTH_REQUIRED' : 'TRUECONF_HTTP_ERROR';
    error.status = Number(response.status || 0);
    error.responseText = rawText.slice(0, 1200);
    throw error;
  }
  if (!isPlainRecord(parsed)) {
    const error = new Error('TrueConf вернул неожиданный ответ.');
    error.code = 'TRUECONF_PARSE_ERROR';
    error.responseText = rawText.slice(0, 1200);
    throw error;
  }
  return {
    baseUrl,
    requestUrl,
    parsed
  };
}

async function fetchTrueconfRooms(event = null, payload = {}) {
  const requestPayload = isPlainRecord(payload) ? payload : {};
  let firstError = null;
  let rooms = [];
  let sourceType = '';
  try {
    const response = await requestTrueconfJson(event, requestPayload, '/api/v3.10/conference-meetings');
    rooms = collectTrueconfRoomRecords(response.parsed, 'conference-meetings');
    sourceType = 'conference-meetings';
    if (rooms.length) {
      return {
        ok: true,
        baseUrl: response.baseUrl,
        sourceType,
        rooms,
        fetchedAt: Date.now()
      };
    }
  } catch (error) {
    firstError = error;
  }

  try {
    const response = await requestTrueconfJson(event, requestPayload, buildTrueconfListPath(requestPayload));
    rooms = collectTrueconfRoomRecords(response.parsed, 'conferences')
      .sort((left, right) => String(left.title || '').localeCompare(String(right.title || ''), 'ru'));
    sourceType = 'conferences';
    return {
      ok: true,
      baseUrl: response.baseUrl,
      sourceType,
      rooms,
      fetchedAt: Date.now()
    };
  } catch (error) {
    if (
      firstError
      && String(firstError.code || '').trim() === 'TRUECONF_AUTH_REQUIRED'
      && String(error?.code || '').trim() !== 'TRUECONF_AUTH_REQUIRED'
    ) {
      throw firstError;
    }
    throw error;
  }
}

async function fetchTrueconfRoomDeeplink(event = null, payload = {}) {
  const requestPayload = isPlainRecord(payload) ? payload : {};
  const roomId = pickFirstTrueconfString(
    requestPayload.roomId || requestPayload.conferenceId || '',
    180
  );
  if (!roomId) {
    const error = new Error('Не выбрана комната TrueConf.');
    error.code = 'TRUECONF_ROOM_INVALID';
    throw error;
  }
  const fallbackBaseUrl = normalizeTrueconfBaseUrl(requestPayload.baseUrl || requestPayload.url || '');
  const publicRoomLink = buildTrueconfRoomPublicUrl(fallbackBaseUrl, roomId);
  if (publicRoomLink) {
    return {
      ok: true,
      baseUrl: fallbackBaseUrl,
      roomId,
      roomLink: publicRoomLink,
      deeplinks: {
        default: publicRoomLink,
        web: publicRoomLink
      },
      fetchedAt: Date.now()
    };
  }
  const response = await requestTrueconfJson(
    event,
    requestPayload,
    `/api/v4/conferences/${encodeURIComponent(roomId)}/deeplinks`,
    { timeoutMs: 12000 }
  );
  const deeplinks = isPlainRecord(response.parsed?.deeplinks) ? response.parsed.deeplinks : {};
  const roomLink = pickFirstTrueconfString([
    deeplinks.default,
    deeplinks.desktop,
    deeplinks.web,
    deeplinks.android,
    deeplinks.ios
  ], 4096);
  if (!roomLink) {
    const error = new Error('TrueConf не вернул ссылку для выбранной комнаты.');
    error.code = 'TRUECONF_DEEPLINK_MISSING';
    throw error;
  }
  return {
    ok: true,
    baseUrl: response.baseUrl,
    roomId,
    roomLink,
    deeplinks,
    fetchedAt: Date.now()
  };
}

function buildTrueconfErrorPayload(error = null, fallbackCode = 'TRUECONF_ERROR') {
  const code = trimText(error?.code || fallbackCode, 64).trim() || fallbackCode;
  const message = trimText(
    error?.message || 'Не удалось выполнить запрос TrueConf.',
    240
  ).trim() || 'Не удалось выполнить запрос TrueConf.';
  return {
    ok: false,
    code,
    error: message,
    status: Math.max(0, Number(error?.status || 0) || 0)
  };
}

function buildTrueconfAuthUrl(baseUrl = '') {
  const normalizedBase = normalizeTrueconfBaseUrl(baseUrl);
  if (!normalizedBase) return '';
  try {
    const parsed = new URL('/user/general', `${normalizedBase}/`);
    parsed.search = '';
    parsed.hash = '';
    return parsed.toString();
  } catch {
    return normalizedBase;
  }
}

function normalizeTrueconfBridgeBaseUrl(value = '', fallbackBaseUrl = '') {
  const raw = trimText(value || '', 4096).trim();
  if (!raw) {
    return normalizeTrueconfBaseUrl(fallbackBaseUrl || '');
  }
  const candidate = raw.includes('://')
    ? raw
    : (/:\d+(?:\/)?$/u.test(raw) ? `http://${raw}` : `https://${raw}`);
  try {
    const parsed = new URL(candidate);
    if (!['http:', 'https:'].includes(parsed.protocol)) return '';
    if (!isAllowedTrueconfHostname(parsed.hostname)) return '';
    parsed.username = '';
    parsed.password = '';
    parsed.pathname = '/';
    parsed.search = '';
    parsed.hash = '';
    return parsed.toString().replace(/\/$/, '');
  } catch {
    return '';
  }
}

function getTrueconfBridgeCandidateLabel(baseUrl = '') {
  try {
    const parsed = new URL(baseUrl);
    return parsed.host || parsed.href;
  } catch {
    return trimText(baseUrl || '', 120);
  }
}

function buildTrueconfBridgeBaseCandidates(settings = null) {
  const normalized = normalizeTrueconfChatSettings(settings);
  const candidates = [];
  const seen = new Set();
  const addCandidate = (value = '') => {
    const normalizedUrl = normalizeTrueconfBridgeBaseUrl(value || '', '');
    if (!normalizedUrl || seen.has(normalizedUrl)) return false;
    seen.add(normalizedUrl);
    candidates.push(normalizedUrl);
    return true;
  };

  const rawSeed = normalized.rawBridgeUrl || normalized.rawBaseUrl || '';
  const rawHasProtocol = /:\/\//.test(rawSeed);
  let rawHost = '';
  try {
    const parsedRaw = rawSeed
      ? new URL(rawHasProtocol ? rawSeed : `http://${rawSeed}`)
      : null;
    rawHost = parsedRaw && isAllowedTrueconfHostname(parsedRaw.hostname) ? parsedRaw.hostname : '';
    if (rawHost && !rawHasProtocol) {
      addCandidate(`http://${rawHost}`);
    }
  } catch {
    rawHost = '';
  }

  addCandidate(normalized.rawBridgeUrl || '');
  addCandidate(normalized.rawBaseUrl || '');
  addCandidate(normalized.bridgeUrl || '');
  addCandidate(normalized.baseUrl || '');

  const seedUrl = normalized.bridgeUrl || normalized.baseUrl || '';
  let parsed = null;
  try {
    parsed = seedUrl ? new URL(seedUrl) : null;
  } catch {
    parsed = null;
  }
  if (parsed && isAllowedTrueconfHostname(parsed.hostname)) {
    const host = parsed.hostname;
    const explicitPort = trimText(parsed.port || '', 12);
    if (explicitPort) {
      addCandidate(`http://${host}:${explicitPort}`);
      addCandidate(`https://${host}:${explicitPort}`);
    }
    TRUECONF_CHAT_BRIDGE_FALLBACK_PORTS.forEach((port) => {
      addCandidate(`http://${host}:${port}`);
    });
    addCandidate(`https://${host}`);
    addCandidate(`http://${host}`);
  }

  return candidates;
}

function normalizeTrueconfChatSettings(source = null) {
  const input = isPlainRecord(source) ? source : {};
  const rawBaseUrl = trimText(input.baseUrl || input.url || input.trueconfBaseUrl || '', 4096).trim();
  const rawBridgeUrl = trimText(input.bridgeUrl || input.bridgeBaseUrl || input.bridgeApiUrl || '', 4096).trim();
  const baseUrl = normalizeTrueconfBaseUrl(rawBaseUrl);
  return {
    rawBaseUrl,
    rawBridgeUrl,
    baseUrl,
    bridgeUrl: normalizeTrueconfBridgeBaseUrl(
      rawBridgeUrl,
      baseUrl
    ),
    username: trimText(input.username || input.login || input.user || '', 180).trim(),
    password: trimText(input.password || input.pass || '', 1200)
  };
}

function normalizeTrueconfTimestamp(value = 0) {
  const numeric = Number(value || 0);
  if (!Number.isFinite(numeric) || numeric <= 0) return 0;
  if (numeric < 10000000000) return Math.round(numeric * 1000);
  return Math.round(numeric);
}

function normalizeTrueconfChatId(value = '') {
  const raw = trimText(value || '', 240).trim();
  return raw.replace(/^tc:/i, '').trim();
}

function buildTrueconfChatId(value = '') {
  const raw = normalizeTrueconfChatId(value);
  return raw ? `${TRUECONF_CHAT_PREFIX}${raw}` : '';
}

function getTrueconfChatAuthCacheKey(settings = null) {
  const normalized = normalizeTrueconfChatSettings(settings);
  const serverKey = normalized.baseUrl || normalized.rawBaseUrl;
  if (!serverKey || !normalized.username) return '';
  return crypto
    .createHash('sha256')
    .update(`${serverKey}\n${normalized.bridgeUrl || normalized.rawBridgeUrl || normalized.baseUrl || normalized.rawBaseUrl}\n${normalized.username}`)
    .digest('hex')
    .slice(0, 48);
}

function getStoredTrueconfChatToken(settings = null) {
  const cacheKey = getTrueconfChatAuthCacheKey(settings);
  if (!cacheKey) return null;
  const record = authStateStore.get(`${TRUECONF_CHAT_AUTH_STORE_KEY}.${cacheKey}`) || null;
  if (!isPlainRecord(record)) return null;
  const accessToken = trimText(record.accessToken || record.access_token || '', 12000).trim();
  const tokenType = trimText(record.tokenType || record.token_type || 'JWT', 40).trim() || 'JWT';
  const expiresAt = normalizeTrueconfTimestamp(record.expiresAt || record.expires_at || 0);
  if (!accessToken || (expiresAt && expiresAt <= Date.now() + 60000)) return null;
  return {
    accessToken,
    tokenType,
    expiresAt,
    userId: trimText(record.userId || '', 240).trim(),
    bridgeUrl: normalizeTrueconfBridgeBaseUrl(record.bridgeUrl || record.bridge_url || '', '')
  };
}

function setStoredTrueconfChatToken(settings = null, tokenRecord = null) {
  const cacheKey = getTrueconfChatAuthCacheKey(settings);
  if (!cacheKey || !isPlainRecord(tokenRecord)) return false;
  const accessToken = trimText(tokenRecord.accessToken || tokenRecord.access_token || '', 12000).trim();
  if (!accessToken) return false;
  authStateStore.set(`${TRUECONF_CHAT_AUTH_STORE_KEY}.${cacheKey}`, {
    accessToken,
    tokenType: trimText(tokenRecord.tokenType || tokenRecord.token_type || 'JWT', 40).trim() || 'JWT',
    expiresAt: normalizeTrueconfTimestamp(tokenRecord.expiresAt || tokenRecord.expires_at || 0),
    userId: trimText(tokenRecord.userId || '', 240).trim(),
    bridgeUrl: normalizeTrueconfBridgeBaseUrl(tokenRecord.bridgeUrl || tokenRecord.bridge_url || '', ''),
    updatedAt: Date.now()
  });
  return true;
}

function clearStoredTrueconfChatToken(settings = null) {
  const cacheKey = getTrueconfChatAuthCacheKey(settings);
  if (!cacheKey) return false;
  authStateStore.delete(`${TRUECONF_CHAT_AUTH_STORE_KEY}.${cacheKey}`);
  return true;
}

function buildTrueconfBridgeUrl(baseUrl = '', pathname = '') {
  const normalizedBase = normalizeTrueconfBridgeBaseUrl(baseUrl);
  const safePathname = String(pathname || '').trim();
  if (!normalizedBase || !safePathname) return '';
  try {
    const parsed = new URL(safePathname, `${normalizedBase}/`);
    if (!['http:', 'https:'].includes(parsed.protocol) || !isAllowedTrueconfHostname(parsed.hostname)) return '';
    parsed.username = '';
    parsed.password = '';
    return parsed.toString();
  } catch {
    return '';
  }
}

function buildTrueconfBridgeWebSocketUrl(baseUrl = '') {
  const normalizedBase = normalizeTrueconfBridgeBaseUrl(baseUrl);
  if (!normalizedBase) return '';
  try {
    const parsed = new URL('/websocket/chat_bot/', `${normalizedBase}/`);
    if (!isAllowedTrueconfHostname(parsed.hostname)) return '';
    parsed.protocol = parsed.protocol === 'http:' ? 'ws:' : 'wss:';
    parsed.username = '';
    parsed.password = '';
    parsed.search = '';
    parsed.hash = '';
    return parsed.toString();
  } catch {
    return '';
  }
}

function looksLikeTrueconfHtmlResponse(rawText = '', contentType = '') {
  const type = trimText(contentType || '', 160).toLowerCase();
  const text = String(rawText || '').trim().slice(0, 500).toLowerCase();
  return type.includes('text/html') || /^<!doctype\s+html/i.test(text) || /^<html[\s>]/i.test(text);
}

function buildTrueconfBridgeNonJsonError(response = null, rawText = '', fallbackMessage = '') {
  const status = Number(response?.status || 0);
  const contentType = (() => {
    try {
      return trimText(response?.headers?.get?.('content-type') || '', 160);
    } catch {
      return '';
    }
  })();
  const isHtml = looksLikeTrueconfHtmlResponse(rawText, contentType);
  const textPreview = stripTrueconfHtmlText(rawText || '');
  const message = isHtml
    ? 'TrueConf Web открывается, но Bridge API вернул веб-страницу вместо JSON. Проверьте, что на сервере включён TrueConf Bridge/Chatbot Connector и Web Manager проксирует /bridge/api/.'
    : (
      trimText(fallbackMessage || textPreview || '', 260).trim()
      || (status ? `TrueConf Bridge вернул ${status}.` : 'TrueConf Bridge вернул неожиданный ответ.')
    );
  const error = new Error(message);
  error.code = isHtml ? 'TRUECONF_CHAT_BRIDGE_HTML_RESPONSE' : 'TRUECONF_CHAT_AUTH_FAILED';
  error.status = status;
  error.responseText = trimText(rawText || '', 1200);
  error.contentType = contentType;
  return error;
}

async function fetchTrueconfChatTokenFromBridge(settings = null, bridgeBaseUrl = '', options = {}) {
  const tokenUrl = buildTrueconfBridgeUrl(bridgeBaseUrl, '/bridge/api/client/v1/oauth/token');
  if (!tokenUrl) {
    const error = new Error('Не удалось подготовить URL авторизации TrueConf Bridge.');
    error.code = 'TRUECONF_CHAT_URL_INVALID';
    throw error;
  }
  const response = await fetchWithResolvedSession(getPersistentYuchatSession(), tokenUrl, {
    method: 'POST',
    timeoutMs: Math.max(2500, Math.min(20000, Number(options.timeoutMs || TRUECONF_CHAT_BRIDGE_DISCOVERY_TIMEOUT_MS) || TRUECONF_CHAT_BRIDGE_DISCOVERY_TIMEOUT_MS)),
    timeoutMessage: 'Не удалось дождаться ответа авторизации TrueConf.',
    headers: {
      Accept: 'application/json',
      'Content-Type': 'application/json'
    },
    body: JSON.stringify({
      client_id: 'chat_bot',
      grant_type: 'password',
      username: settings.username,
      password: settings.password
    }),
    redirect: 'follow'
  });
  const { rawText, parsed } = await readJsonResponse(response);
  if (!response.ok || !isPlainRecord(parsed) || !trimText(parsed.access_token || '', 12000).trim()) {
    if (!isPlainRecord(parsed) && rawText) {
      throw buildTrueconfBridgeNonJsonError(response, rawText);
    }
    const errorText = trimText(
      parsed?.error_description
      || parsed?.error?.message
      || parsed?.message
      || rawText,
      220
    ).trim();
    const error = new Error(errorText || `TrueConf Bridge вернул ${response.status}.`);
    error.code = [400, 401, 403].includes(Number(response.status || 0))
      ? 'TRUECONF_CHAT_AUTH_REQUIRED'
      : 'TRUECONF_CHAT_AUTH_FAILED';
    error.status = Number(response.status || 0);
    throw error;
  }
  return {
    accessToken: trimText(parsed.access_token || '', 12000).trim(),
    tokenType: trimText(parsed.token_type || 'JWT', 40).trim() || 'JWT',
    expiresAt: normalizeTrueconfTimestamp(parsed.expires_at || 0) || (Date.now() + 30 * 24 * 60 * 60 * 1000),
    userId: '',
    bridgeUrl: normalizeTrueconfBridgeBaseUrl(bridgeBaseUrl, '')
  };
}

function buildTrueconfBridgeDiscoveryError(attempts = []) {
  const authError = attempts.find((attempt) => String(attempt?.error?.code || '') === 'TRUECONF_CHAT_AUTH_REQUIRED');
  if (authError?.error) return authError.error;
  const parts = attempts
    .slice(0, 5)
    .map((attempt) => {
      const label = getTrueconfBridgeCandidateLabel(attempt?.bridgeUrl || '');
      const code = trimText(attempt?.error?.code || '', 80);
      const message = trimText(attempt?.error?.message || 'нет ответа', 120);
      return `${label}: ${code === 'TRUECONF_CHAT_BRIDGE_HTML_RESPONSE' ? 'HTML вместо API' : message}`;
    })
    .filter(Boolean);
  const hint = 'Нативный TrueConf-клиент может быть подключён через порт 4307, но это другой протокол; для чатов в YuChat нужен Chatbot Connector/Bridge API на 4309 или HTTPS-прокси /bridge/api/.';
  const error = new Error(parts.length
    ? `Не удалось найти рабочий TrueConf Bridge. Проверил: ${parts.join('; ')}. ${hint}`
    : `Не удалось найти рабочий TrueConf Bridge. ${hint}`);
  error.code = 'TRUECONF_CHAT_BRIDGE_DISCOVERY_FAILED';
  return error;
}

async function requestTrueconfChatToken(rawSettings = null, options = {}) {
  const settings = normalizeTrueconfChatSettings(rawSettings);
  if (!(settings.baseUrl || settings.rawBaseUrl) || !settings.username) {
    const error = new Error('Укажите сервер и логин TrueConf.');
    error.code = 'TRUECONF_CHAT_SETTINGS_INVALID';
    throw error;
  }
  const cached = options.force !== true ? getStoredTrueconfChatToken(settings) : null;
  if (cached) return cached;
  if (!settings.password) {
    const error = new Error('Для API чатов TrueConf нужен пароль пользователя или сохранённый токен.');
    error.code = 'TRUECONF_CHAT_CREDENTIALS_REQUIRED';
    throw error;
  }
  const candidates = buildTrueconfBridgeBaseCandidates(settings);
  const attempts = [];
  for (const bridgeUrl of candidates) {
    try {
      const tokenRecord = await fetchTrueconfChatTokenFromBridge(settings, bridgeUrl, options);
      setStoredTrueconfChatToken(settings, tokenRecord);
      return tokenRecord;
    } catch (error) {
      attempts.push({ bridgeUrl, error });
      if (String(error?.code || '') === 'TRUECONF_CHAT_AUTH_REQUIRED') {
        throw error;
      }
    }
  }
  if (!attempts.length) {
    const error = new Error('Не удалось подготовить варианты подключения к TrueConf Bridge.');
    error.code = 'TRUECONF_CHAT_URL_INVALID';
    throw error;
  }
  throw buildTrueconfBridgeDiscoveryError(attempts);
}

function getTrueconfWebSocketConstructor() {
  try {
    if (typeof WebSocket === 'function') return WebSocket;
  } catch {
    return null;
  }
  return null;
}

function addTrueconfWebSocketListener(socket = null, eventName = '', handler = null) {
  if (!socket || typeof handler !== 'function') return false;
  if (typeof socket.addEventListener === 'function') {
    socket.addEventListener(eventName, handler);
    return true;
  }
  if (typeof socket.on === 'function') {
    socket.on(eventName, handler);
    return true;
  }
  return false;
}

async function normalizeTrueconfWebSocketData(data = null) {
  if (typeof data === 'string') return data;
  if (Buffer.isBuffer(data)) return data.toString('utf8');
  if (data instanceof ArrayBuffer) return Buffer.from(data).toString('utf8');
  if (ArrayBuffer.isView(data)) {
    return Buffer.from(data.buffer, data.byteOffset, data.byteLength).toString('utf8');
  }
  if (data && typeof data.text === 'function') {
    return await data.text();
  }
  return String(data || '');
}

function buildTrueconfBridgeError(message = null, fallbackCode = 'TRUECONF_CHAT_BRIDGE_ERROR') {
  const errorCode = trimText(
    message?.errorCode
    || message?.payload?.errorCode
    || message?.error?.code
    || fallbackCode,
    80
  ).trim() || fallbackCode;
  const errorText = trimText(
    message?.errorMessage
    || message?.payload?.errorMessage
    || message?.payload?.message
    || message?.error?.message
    || message?.message
    || 'TrueConf Bridge вернул ошибку.',
    240
  ).trim() || 'TrueConf Bridge вернул ошибку.';
  const error = new Error(errorText);
  error.code = errorCode;
  return error;
}

async function sendTrueconfBridgeCommand(rawSettings = null, method = '', payload = {}, options = {}) {
  const settings = normalizeTrueconfChatSettings(rawSettings);
  const command = trimText(method || '', 80).trim();
  if (!(settings.baseUrl || settings.rawBaseUrl) || !settings.username || !command) {
    const error = new Error('Некорректные параметры команды TrueConf.');
    error.code = 'TRUECONF_CHAT_COMMAND_INVALID';
    throw error;
  }
  const tokenRecord = await requestTrueconfChatToken(settings, options);
  const wsUrl = buildTrueconfBridgeWebSocketUrl(tokenRecord.bridgeUrl || settings.bridgeUrl || settings.baseUrl);
  const WebSocketImpl = getTrueconfWebSocketConstructor();
  if (!wsUrl || !WebSocketImpl) {
    const error = new Error('WebSocket для TrueConf Bridge недоступен в текущей сборке.');
    error.code = 'TRUECONF_CHAT_WEBSOCKET_UNAVAILABLE';
    throw error;
  }
  const timeoutMs = Math.max(3000, Math.min(60000, Number(options.timeoutMs || TRUECONF_CHAT_WS_TIMEOUT_MS) || TRUECONF_CHAT_WS_TIMEOUT_MS));

  return new Promise((resolve, reject) => {
    let socket = null;
    let settled = false;
    let authenticated = false;
    let selfUserId = trimText(tokenRecord.userId || '', 240).trim();
    let nextId = 1;
    const authId = nextId++;
    const requestId = nextId++;
    const timer = setTimeout(() => {
      finish(false, Object.assign(new Error('Не удалось дождаться ответа TrueConf Bridge.'), {
        code: 'TRUECONF_CHAT_TIMEOUT'
      }));
    }, timeoutMs);

    const finish = (ok, value) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      try {
        if (socket && typeof socket.close === 'function') {
          socket.close();
        }
      } catch {
        // ignore close failures
      }
      if (ok) {
        resolve(value);
      } else {
        reject(value);
      }
    };

    const sendPacket = (packet = {}) => {
      try {
        socket.send(JSON.stringify(packet));
      } catch (error) {
        finish(false, error);
      }
    };

    const handleResponseMessage = async (event = null) => {
      if (settled) return;
      let message = null;
      try {
        const text = await normalizeTrueconfWebSocketData(event?.data ?? event);
        message = text ? JSON.parse(text) : null;
      } catch {
        return;
      }
      if (!isPlainRecord(message)) return;
      if (message.type === 1 && message.id) {
        sendPacket({
          type: 2,
          id: message.id
        });
      }
      if (message.errorCode || message.payload?.errorCode || message.error) {
        finish(false, buildTrueconfBridgeError(message));
        return;
      }
      if (message.id === authId && message.type === 2) {
        authenticated = true;
        selfUserId = trimText(message.payload?.userId || selfUserId || '', 240).trim();
        if (selfUserId) {
          setStoredTrueconfChatToken(settings, {
            ...tokenRecord,
            bridgeUrl: tokenRecord.bridgeUrl || settings.bridgeUrl || settings.baseUrl,
            userId: selfUserId
          });
        }
        sendPacket({
          type: 1,
          id: requestId,
          method: command,
          payload: isPlainRecord(payload) ? payload : {}
        });
        return;
      }
      if (message.id === requestId && message.type === 2) {
        finish(true, {
          ok: true,
          payload: message.payload,
          userId: selfUserId,
          method: command
        });
      }
    };

    try {
      socket = new WebSocketImpl(wsUrl, 'json.v1');
      addTrueconfWebSocketListener(socket, 'open', () => {
        sendPacket({
          type: 1,
          id: authId,
          method: 'auth',
          payload: {
            token: tokenRecord.accessToken,
            tokenType: tokenRecord.tokenType || 'JWT',
            receiveUnread: false,
            receiveSystemMessageEnvelopes: true
          }
        });
      });
      addTrueconfWebSocketListener(socket, 'message', handleResponseMessage);
      addTrueconfWebSocketListener(socket, 'error', () => {
        finish(false, Object.assign(new Error('Не удалось подключиться к TrueConf Bridge.'), {
          code: 'TRUECONF_CHAT_WEBSOCKET_ERROR'
        }));
      });
      addTrueconfWebSocketListener(socket, 'close', () => {
        if (!settled && !authenticated) {
          finish(false, Object.assign(new Error('TrueConf Bridge закрыл соединение до авторизации.'), {
            code: 'TRUECONF_CHAT_WEBSOCKET_CLOSED'
          }));
        }
      });
    } catch (error) {
      finish(false, error);
    }
  });
}

function getTrueconfChatTypeName(value = null) {
  const numeric = Math.trunc(Number(value || 0) || 0);
  if (numeric === 1) return 'direct';
  if (numeric === 2) return 'group';
  if (numeric === 3) return 'system';
  if (numeric === 5) return 'favorites';
  if (numeric === 6) return 'channel';
  return 'chat';
}

function normalizeTrueconfAuthorId(value = '') {
  return trimText(value || '', 240).trim().toLowerCase();
}

function stripTrueconfHtmlText(value = '') {
  return trimText(String(value || '').replace(/<[^>]*>/g, ' ').replace(/\s+/g, ' '), 2000).trim();
}

function buildTrueconfEnvelopeText(envelope = null) {
  if (!isPlainRecord(envelope)) return '';
  const content = isPlainRecord(envelope.content) ? envelope.content : {};
  const directText = trimText(content.text || envelope.text || '', 2000).trim();
  if (directText) {
    const parseMode = trimText(content.parseMode || envelope.parseMode || '', 40).toLowerCase();
    return parseMode === 'html' ? stripTrueconfHtmlText(directText) : directText;
  }
  const fileName = trimText(content.name || content.fileName || '', 240).trim();
  if (fileName) return `Файл: ${fileName}`;
  const type = Math.trunc(Number(envelope.type || 0) || 0);
  if (type === 1) return 'Участник добавлен в чат';
  if (type === 2) return 'Участник удалён из чата';
  if (type === 21) return 'Название чата изменено';
  if (type === 22) return 'Аватар чата изменён';
  if (type === 23) return 'История чата очищена';
  if (type === 110) return 'Изменена роль участника';
  return type > 0 && type < 200 ? 'Системное сообщение TrueConf' : '';
}

function normalizeTrueconfEnvelope(envelope = null, chatId = '', settings = null, selfUserId = '') {
  if (!isPlainRecord(envelope)) return null;
  const messageId = trimText(envelope.messageId || envelope.id || '', 180).trim();
  if (!messageId) return null;
  const rawChatId = normalizeTrueconfChatId(envelope.chatId || chatId || '');
  const normalizedChatId = buildTrueconfChatId(rawChatId);
  if (!normalizedChatId) return null;
  const authorId = trimText(envelope.author?.id || envelope.authorId || envelope.senderId || '', 240).trim();
  const normalizedAuthor = normalizeTrueconfAuthorId(authorId);
  const normalizedSelf = normalizeTrueconfAuthorId(selfUserId || settings?.username || '');
  const isMine = Boolean(normalizedAuthor && normalizedSelf && normalizedAuthor === normalizedSelf);
  const text = buildTrueconfEnvelopeText(envelope);
  const timestamp = normalizeTrueconfTimestamp(envelope.timestamp || envelope.createdAt || 0) || Date.now();
  return {
    id: messageId,
    workspaceId: 'trueconf',
    chatId: normalizedChatId,
    text,
    formattedText: text,
    authorName: isMine ? 'Вы' : (authorId || 'TrueConf'),
    authorMemberId: authorId ? `trueconf:${authorId}` : 'trueconf:system',
    timestamp,
    isMine,
    deliveryStatus: isMine ? 'sent' : '',
    replyToMessageId: trimText(envelope.replyMessageId || '', 180).trim(),
    attachments: [],
    raw: {
      ...envelope,
      source: 'trueconf'
    }
  };
}

function normalizeTrueconfChatRecord(record = null, settings = null, selfUserId = '') {
  if (!isPlainRecord(record)) return null;
  const rawChatId = normalizeTrueconfChatId(record.chatId || record.id || '');
  const chatId = buildTrueconfChatId(rawChatId);
  if (!chatId) return null;
  const chatType = getTrueconfChatTypeName(record.chatType || record.type || 0);
  const title = trimText(record.title || record.name || (chatType === 'favorites' ? 'Избранное' : '') || rawChatId, 180).trim() || 'TrueConf';
  const lastMessage = normalizeTrueconfEnvelope(
    isPlainRecord(record.lastMessage) ? { ...record.lastMessage, chatId: rawChatId } : null,
    rawChatId,
    settings,
    selfUserId
  );
  const unreadCount = Math.max(0, Math.trunc(Number(record.unreadMessages ?? record.unreadCount ?? 0) || 0));
  const updatedAt = Math.max(
    normalizeTrueconfTimestamp(record.updatedAt || 0),
    Number(lastMessage?.timestamp || 0),
    0
  );
  return {
    workspaceId: 'trueconf',
    workspaceTitle: 'TrueConf',
    chatId,
    title,
    searchText: [
      title,
      'TrueConf',
      'Труконф',
      chatType,
      rawChatId,
      lastMessage?.text || ''
    ].filter(Boolean).join(' '),
    avatarUrl: '',
    unreadCount,
    previewText: trimText(lastMessage?.text || '', 220),
    previewAuthor: trimText(lastMessage?.authorName || '', 120),
    previewAuthorMemberId: trimText(lastMessage?.authorMemberId || '', 180),
    previewMessageId: trimText(lastMessage?.id || '', 180),
    previewIsMine: lastMessage?.isMine === true,
    previewTimestamp: updatedAt,
    updatedAt,
    memberIds: [],
    directMemberId: chatType === 'direct' ? `trueconf:${title}` : '',
    isDirect: chatType === 'direct',
    isTrueconf: true,
    trueconfType: chatType,
    type: chatType,
    sourceLabel: 'TrueConf',
    rawChat: {
      ...record,
      source: 'trueconf',
      trueconfType: chatType
    }
  };
}

async function checkTrueconfChatConnection(payload = {}) {
  try {
    const settings = normalizeTrueconfChatSettings(payload?.settings || payload);
    const result = await sendTrueconfBridgeCommand(settings, 'getChats', {
      count: 1,
      page: 1
    }, { timeoutMs: TRUECONF_CHAT_WS_TIMEOUT_MS, force: payload?.forceAuth === true });
    const chats = Array.isArray(result.payload) ? result.payload : [];
    return {
      ok: true,
      authorized: true,
      userId: result.userId || '',
      chatCountProbe: chats.length,
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTrueconfErrorPayload(error, 'TRUECONF_CHAT_STATE_ERROR');
  }
}

async function listTrueconfChats(payload = {}) {
  try {
    const settings = normalizeTrueconfChatSettings(payload?.settings || payload);
    const count = Math.max(1, Math.min(
      TRUECONF_CHAT_MAX_PAGE_SIZE,
      Math.trunc(Number(payload?.limit || payload?.count || TRUECONF_CHAT_DEFAULT_PAGE_SIZE) || TRUECONF_CHAT_DEFAULT_PAGE_SIZE)
    ));
    const result = await sendTrueconfBridgeCommand(settings, 'getChats', {
      count,
      page: Math.max(1, Math.trunc(Number(payload?.page || 1) || 1))
    });
    const records = Array.isArray(result.payload) ? result.payload : [];
    const chats = records
      .map((record) => normalizeTrueconfChatRecord(record, settings, result.userId || ''))
      .filter(Boolean)
      .sort((left, right) => Number(right.updatedAt || 0) - Number(left.updatedAt || 0));
    return {
      ok: true,
      authorized: true,
      userId: result.userId || '',
      dialogs: chats,
      chats,
      hasMore: records.length >= count,
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTrueconfErrorPayload(error, 'TRUECONF_CHAT_LIST_ERROR');
  }
}

async function listTrueconfMessages(payload = {}) {
  try {
    const settings = normalizeTrueconfChatSettings(payload?.settings || payload);
    const rawChatId = normalizeTrueconfChatId(payload?.chatId || payload?.peer || '');
    if (!rawChatId) {
      const error = new Error('Не удалось определить чат TrueConf.');
      error.code = 'TRUECONF_CHAT_ID_INVALID';
      throw error;
    }
    const count = Math.max(1, Math.min(
      TRUECONF_CHAT_MAX_PAGE_SIZE,
      Math.trunc(Number(payload?.count || payload?.limit || 80) || 80)
    ));
    const requestPayload = {
      chatId: rawChatId,
      count
    };
    const fromMessageId = trimText(payload?.fromMessageId || '', 180).trim();
    if (fromMessageId) requestPayload.fromMessageId = fromMessageId;
    const result = await sendTrueconfBridgeCommand(settings, 'getChatHistory', requestPayload);
    const historyPayload = isPlainRecord(result.payload) ? result.payload : {};
    const rawMessages = Array.isArray(historyPayload.messages) ? historyPayload.messages : [];
    const items = rawMessages
      .map((message) => normalizeTrueconfEnvelope(message, rawChatId, settings, result.userId || ''))
      .filter(Boolean)
      .sort((left, right) => Number(left.timestamp || 0) - Number(right.timestamp || 0));
    return {
      ok: true,
      authorized: true,
      userId: result.userId || '',
      items,
      hasMore: rawMessages.length >= count,
      loadedCount: count,
      resolvedChatId: buildTrueconfChatId(historyPayload.chatId || rawChatId),
      resolvedWorkspaceId: 'trueconf',
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTrueconfErrorPayload(error, 'TRUECONF_CHAT_MESSAGES_ERROR');
  }
}

async function sendTrueconfMessage(payload = {}) {
  try {
    const settings = normalizeTrueconfChatSettings(payload?.settings || payload);
    const rawChatId = normalizeTrueconfChatId(payload?.chatId || payload?.peer || '');
    const text = trimText(payload?.text || payload?.message || '', 6000).trim();
    if (!rawChatId || !text) {
      const error = new Error('Не удалось отправить пустое сообщение TrueConf.');
      error.code = 'TRUECONF_CHAT_MESSAGE_EMPTY';
      throw error;
    }
    const requestPayload = {
      chatId: rawChatId,
      content: {
        text,
        parseMode: 'text'
      }
    };
    const replyMessageId = trimText(payload?.inReplyToMessageId || payload?.replyMessageId || '', 180).trim();
    if (replyMessageId) requestPayload.replyMessageId = replyMessageId;
    const result = await sendTrueconfBridgeCommand(settings, 'sendMessage', requestPayload, {
      timeoutMs: Math.max(TRUECONF_CHAT_WS_TIMEOUT_MS, 30000)
    });
    const sent = isPlainRecord(result.payload) ? result.payload : {};
    const messageId = trimText(sent.messageId || payload?.clientMessageId || `trueconf-${Date.now()}`, 180).trim();
    const message = normalizeTrueconfEnvelope({
      chatId: sent.chatId || rawChatId,
      messageId,
      timestamp: sent.timestamp || Date.now(),
      author: {
        id: result.userId || settings.username,
        type: 1
      },
      type: 200,
      content: {
        text,
        parseMode: 'text'
      },
      replyMessageId
    }, rawChatId, settings, result.userId || settings.username);
    return {
      ok: true,
      authorized: true,
      userId: result.userId || '',
      message,
      loadedAt: Date.now()
    };
  } catch (error) {
    return buildTrueconfErrorPayload(error, 'TRUECONF_CHAT_SEND_ERROR');
  }
}

function logoutTrueconfChatIntegration(payload = {}) {
  const settings = normalizeTrueconfChatSettings(payload?.settings || payload);
  clearStoredTrueconfChatToken(settings);
  return {
    ok: true
  };
}

function revealExternalAuthWindow(windowRef = null, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
    return false;
  }
  try {
    if (windowRef.isMinimized()) {
      windowRef.restore();
    }
  } catch {
    // ignore restore failures
  }
  try {
    if (!windowRef.isVisible()) {
      if (options?.inactive === true && typeof windowRef.showInactive === 'function') {
        windowRef.showInactive();
      } else {
        windowRef.show();
      }
    }
  } catch {
    // ignore show failures
  }
  try {
    windowRef.moveTop();
  } catch {
    // ignore move-to-top failures
  }
  if (options?.focus !== false) {
    try {
      windowRef.focus();
    } catch {
      // ignore focus failures
    }
  }
  return true;
}

function buildExternalAuthFallbackHtml(providerName = 'Сервис', details = {}) {
  const safeProvider = escapeHtml(trimText(providerName || 'Сервис', 60) || 'Сервис');
  const safeUrl = escapeHtml(trimText(details?.url || '', 2200));
  const safeError = escapeHtml(trimText(details?.errorText || '', 260));
  const code = Number(details?.errorCode || 0) || 0;
  const hintText = escapeHtml(trimText(details?.hint || '', 320));
  const title = `${safeProvider}: не удалось открыть страницу входа`;
  const errorLine = safeError || (code ? `Код ошибки загрузки: ${code}` : 'Страница вернула пустой ответ.');
  return `<!doctype html>
<html lang="ru">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>${title}</title>
    <style>
      :root { color-scheme: light; }
      html, body {
        margin: 0;
        width: 100%;
        height: 100%;
        font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        background: #f4f7fb;
        color: #1f2937;
      }
      .shell {
        box-sizing: border-box;
        min-height: 100%;
        display: grid;
        place-items: center;
        padding: 28px;
      }
      .card {
        width: min(760px, 96vw);
        background: #fff;
        border: 1px solid #dbe3ef;
        border-radius: 14px;
        box-shadow: 0 16px 42px rgba(15, 23, 42, 0.12);
        padding: 20px 22px;
      }
      h1 {
        margin: 0 0 10px 0;
        font-size: 20px;
        line-height: 1.35;
      }
      p {
        margin: 0;
        color: #4b5563;
        line-height: 1.5;
      }
      .meta {
        margin-top: 12px;
        padding: 10px 12px;
        border-radius: 10px;
        background: #f8fafc;
        border: 1px solid #e5ebf3;
        font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
        font-size: 12px;
        color: #334155;
        white-space: pre-wrap;
        word-break: break-word;
      }
      .hint {
        margin-top: 12px;
        font-size: 13px;
        color: #1f4d7a;
      }
    </style>
  </head>
  <body>
    <div class="shell">
      <section class="card">
        <h1>${title}</h1>
        <p>Окно открылось, но страница не загрузилась корректно.</p>
        <div class="meta">${errorLine}${safeUrl ? `\nURL: ${safeUrl}` : ''}</div>
        <p class="hint">${hintText || 'Проверьте доступ к корпоративной сети КСПД и повторите попытку авторизации.'}</p>
      </section>
    </div>
  </body>
</html>`;
}

async function revealExternalAuthFailurePage(windowRef = null, providerName = '', details = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) {
    return false;
  }
  const html = buildExternalAuthFallbackHtml(providerName, details);
  const dataUrl = `data:text/html;charset=utf-8,${encodeURIComponent(html)}`;
  try {
    windowRef.__yuAuthFailurePageShown = true;
    await windowRef.loadURL(dataUrl);
    revealExternalAuthWindow(windowRef);
    return true;
  } catch {
    return false;
  }
}

function buildMainWindowLoadFailureHtml(details = {}) {
  const targetUrl = trimText(details?.url || YUCHAT_ENTRY_URL, 2200) || YUCHAT_ENTRY_URL;
  const safeTargetUrl = escapeHtml(targetUrl);
  const safeError = escapeHtml(trimText(details?.errorText || '', 320));
  const errorCode = Number(details?.errorCode || 0) || 0;
  const httpStatus = Number(details?.httpStatus || 0) || 0;
  const httpStatusText = trimText(details?.httpStatusText || '', 120);
  const safeHttpStatusLine = httpStatus
    ? `HTTP status: ${httpStatus}${httpStatusText ? ` ${httpStatusText}` : ''}`
    : '';
  const safeErrorLine = safeError || (errorCode ? `Код ошибки загрузки: ${errorCode}` : 'Страница не вернула содержимое.');
  const retryTargetScriptLiteral = JSON.stringify(targetUrl);
  const safeErrorCode = escapeHtml(errorCode ? String(errorCode) : 'unknown');
  const defaultHint = httpStatus === 403
    ? 'Сервер вернул 403 Forbidden. Обычно это сетевой периметр (КСПД/VPN), ACL или политика доступа по IP/учётке.'
    : 'Обычно причина в недоступности сети КСПД/VPN, DNS или самого сервиса. После восстановления сети нажмите «Повторить загрузку».';
  const safeHint = escapeHtml(trimText(details?.hint || defaultHint, 320));
  return `<!doctype html>
<html lang="ru">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>YuChat: не удалось загрузить страницу</title>
    <style>
      :root { color-scheme: light; }
      html, body {
        margin: 0;
        width: 100%;
        height: 100%;
        font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        background: #e8edf3;
        color: #1d2b3a;
      }
      .shell {
        box-sizing: border-box;
        min-height: 100%;
        display: grid;
        place-items: center;
        padding: 28px;
      }
      .card {
        width: min(860px, 96vw);
        background: #fff;
        border: 1px solid #dbe5f1;
        border-radius: 16px;
        box-shadow: 0 18px 52px rgba(15, 23, 42, 0.14);
        padding: 24px 24px 22px;
      }
      h1 {
        margin: 0;
        font-size: 24px;
        line-height: 1.25;
      }
      p {
        margin: 12px 0 0;
        color: #495b70;
        line-height: 1.55;
      }
      .meta {
        margin-top: 14px;
        padding: 12px 14px;
        border-radius: 12px;
        background: #f6f9fc;
        border: 1px solid #dfe8f2;
        font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
        font-size: 12px;
        color: #32475e;
        white-space: pre-wrap;
        word-break: break-word;
      }
      .actions {
        margin-top: 16px;
        display: flex;
        gap: 10px;
        flex-wrap: wrap;
      }
      button, a {
        border: 0;
        border-radius: 10px;
        padding: 11px 14px;
        font-size: 14px;
        font-weight: 600;
        cursor: pointer;
        text-decoration: none;
      }
      button {
        background: #226fce;
        color: #fff;
      }
      a {
        background: #e8eef6;
        color: #23456c;
      }
      .hint {
        margin-top: 12px;
        font-size: 13px;
        color: #355676;
      }
    </style>
  </head>
  <body>
    <div class="shell">
      <section class="card">
        <h1>Не удалось загрузить рабочую область YuChat</h1>
        <p>Это не артефакт интерфейса: приложение открыло окно, но целевая страница не отдала контент.</p>
        <div class="meta">${safeErrorLine}${safeTargetUrl ? `\nURL: ${safeTargetUrl}` : ''}${safeHttpStatusLine ? `\n${escapeHtml(safeHttpStatusLine)}` : ''}\nError code: ${safeErrorCode}</div>
        <div class="actions">
          <button id="retry-button" type="button">Повторить загрузку</button>
          <a href="${safeTargetUrl}" id="open-url-link">Открыть целевой URL</a>
        </div>
        <p class="hint">${safeHint}</p>
      </section>
    </div>
    <script>
      const retryButton = document.getElementById('retry-button');
      const retryUrl = ${retryTargetScriptLiteral};
      retryButton?.addEventListener('click', () => {
        if (!retryUrl) {
          window.location.reload();
          return;
        }
        window.location.replace(retryUrl);
      });
    </script>
  </body>
</html>`;
}

function getLatestMainFrameStatusForWindow(windowRef = null, maxAgeMs = 120000) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return null;
  const targetContents = windowRef.webContents;
  if (!targetContents || targetContents.isDestroyed()) return null;
  const key = Number(targetContents.id || 0) || 0;
  if (!key) return null;
  const snapshot = latestMainFrameStatusByWebContentsId.get(key) || null;
  if (!snapshot || typeof snapshot !== 'object') return null;
  const capturedAt = Number(snapshot.capturedAt || 0) || 0;
  if (capturedAt > 0 && (Date.now() - capturedAt) > Math.max(1000, Number(maxAgeMs) || 120000)) {
    return null;
  }
  return snapshot;
}

async function revealMainWindowLoadFailurePage(details = {}) {
  if (!(mainWindow instanceof BrowserWindow) || mainWindow.isDestroyed()) {
    return false;
  }
  if (LOCAL_SHELL_REQUESTED) {
    return false;
  }
  const statusSnapshot = getLatestMainFrameStatusForWindow(mainWindow);
  const html = buildMainWindowLoadFailureHtml({
    ...details,
    ...(statusSnapshot
      ? {
          httpStatus: Number(details?.httpStatus || 0) || statusSnapshot.status || 0,
          httpStatusText: trimText(details?.httpStatusText || '', 120) || statusSnapshot.statusText || ''
        }
      : null)
  });
  const dataUrl = `data:text/html;charset=utf-8,${encodeURIComponent(html)}`;
  try {
    await mainWindow.loadURL(dataUrl);
    setStartupSplashState({
      percent: 100,
      phase: 'YuChat недоступен',
      detail: 'Показываем страницу восстановления подключения'
    });
    showMainWindow('main_load_failed');
    return true;
  } catch (error) {
    runtimeWarn('[YuChat] Failed to reveal main-window load failure page:', error);
    return false;
  }
}

function bindExternalAuthWindowDiagnostics(windowRef = null, options = {}) {
  if (!(windowRef instanceof BrowserWindow) || windowRef.isDestroyed()) return;
  if (windowRef.__yuAuthDiagnosticsBound === true) return;
  windowRef.__yuAuthDiagnosticsBound = true;
  const providerName = trimText(options?.providerName || 'Сервис', 80) || 'Сервис';
  const fallbackUrl = trimText(options?.url || '', 2200);
  const timeoutMs = Math.max(5000, Math.min(45000, Number(options?.timeoutMs) || 16000));
  let loadWatchdogTimer = 0;
  let loadSettled = false;
  let latestConsoleIssue = '';

  const clearLoadWatchdog = () => {
    if (!loadWatchdogTimer) return;
    clearTimeout(loadWatchdogTimer);
    loadWatchdogTimer = 0;
  };

  const runAuthWindowProbe = async () => {
    if (!windowRef || windowRef.isDestroyed()) return null;
    try {
      return await windowRef.webContents.executeJavaScript(`(() => {
        const text = String(document.body?.innerText || document.body?.textContent || '').trim();
        const safeNodes = Array.from(document.body?.querySelectorAll('*') || [])
          .filter((node) => {
            if (!(node instanceof HTMLElement)) return false;
            const tag = String(node.tagName || '').toLowerCase();
            return !['script', 'style', 'meta', 'link', 'noscript'].includes(tag);
          });
        const visibleNodes = safeNodes.filter((node) => {
          const rect = node.getBoundingClientRect();
          if (!rect || rect.width < 6 || rect.height < 6) return false;
          const style = window.getComputedStyle(node);
          return (
            style.display !== 'none'
            && style.visibility !== 'hidden'
            && Number(style.opacity || 1) > 0.02
          );
        });
        const interactiveNodes = visibleNodes.filter((node) => (
          node.matches('input, button, a, form, [role="button"], [role="link"], iframe')
        ));
        return {
          readyState: String(document.readyState || ''),
          url: String(location.href || ''),
          title: String(document.title || ''),
          textLength: text.length,
          safeNodeCount: safeNodes.length,
          visibleNodeCount: visibleNodes.length,
          interactiveCount: interactiveNodes.length
        };
      })()`, true);
    } catch {
      return null;
    }
  };

  const isProbeHealthy = (probe = null) => {
    const textLength = Number(probe?.textLength || 0) || 0;
    const visibleNodeCount = Number(probe?.visibleNodeCount || 0) || 0;
    const interactiveCount = Number(probe?.interactiveCount || 0) || 0;
    if (textLength >= 20) return true;
    if (interactiveCount > 0) return true;
    if (visibleNodeCount >= 3) return true;
    return false;
  };

  const decorateAuthFailureText = (text = '') => {
    const base = trimText(String(text || '').trim(), 260);
    const issue = trimText(String(latestConsoleIssue || '').trim(), 260);
    if (!issue) return base;
    if (!base) return `Консоль: ${issue}`;
    return `${base} Консоль: ${issue}`;
  };

  const scheduleLoadWatchdog = (reason = 'load-timeout') => {
    clearLoadWatchdog();
    loadSettled = false;
    loadWatchdogTimer = setTimeout(async () => {
      loadWatchdogTimer = 0;
      if (!windowRef || windowRef.isDestroyed()) return;
      if (windowRef.__yuAuthFailurePageShown === true || loadSettled) return;

      const probe = await runAuthWindowProbe();
      if (isProbeHealthy(probe)) {
        loadSettled = true;
        return;
      }

      await revealExternalAuthFailurePage(windowRef, providerName, {
        errorCode: 0,
        errorText: decorateAuthFailureText(`Страница входа не ответила вовремя (${reason}).`),
        url: trimText(probe?.url || fallbackUrl, 2200),
        hint: 'Проверьте корпоративную сеть КСПД/VPN и повторите авторизацию.'
      });
    }, timeoutMs);
    loadWatchdogTimer.unref?.();
  };

  windowRef.webContents.on('did-fail-load', (_event, errorCode, errorDescription, validatedURL, isMainFrame) => {
    if (!isMainFrame) return;
    if (Number(errorCode || 0) === -3) return;
    loadSettled = true;
    clearLoadWatchdog();
    void revealExternalAuthFailurePage(windowRef, providerName, {
      errorCode,
      errorText: decorateAuthFailureText(errorDescription || ''),
      url: validatedURL || fallbackUrl,
      hint: `Если домен ${fallbackUrl || 'сервиса'} не открывается, подключитесь к сети КСПД.`
    });
  });

  windowRef.webContents.on('did-finish-load', async () => {
    if (!windowRef || windowRef.isDestroyed()) return;
    if (windowRef.__yuAuthFailurePageShown === true) return;
    clearLoadWatchdog();
    try {
      const probe = await runAuthWindowProbe();
      if (isProbeHealthy(probe)) {
        loadSettled = true;
        return;
      }
      await revealExternalAuthFailurePage(windowRef, providerName, {
        errorCode: 0,
        errorText: decorateAuthFailureText('Страница загрузилась пустой.'),
        url: trimText(probe?.url || fallbackUrl, 2200),
        hint: 'Обычно это связано с недоступностью сервиса или корпоративного DNS.'
      });
    } catch {
      // ignore probe failures
    }
  });

  windowRef.webContents.on('did-start-loading', () => {
    scheduleLoadWatchdog('did-start-loading');
  });
  windowRef.webContents.on('did-start-navigation', (_event, _url, _isInPlace, isMainFrame) => {
    if (!isMainFrame) return;
    scheduleLoadWatchdog('did-start-navigation');
  });
  windowRef.webContents.on('console-message', (_event, level, message) => {
    const normalizedMessage = trimText(String(message || '').replace(/\s+/g, ' ').trim(), 260);
    if (!normalizedMessage) return;
    const numericLevel = Number(level || 0) || 0;
    if (numericLevel >= 2 || /error|failed|exception|uncaught|refused|blocked|denied|csp/i.test(normalizedMessage)) {
      latestConsoleIssue = normalizedMessage;
    }
  });
  windowRef.on('closed', () => {
    clearLoadWatchdog();
  });

  scheduleLoadWatchdog('initial-open');
}

async function openTrueconfAuthorizationWindow(event = null, payload = {}) {
  const requestPayload = isPlainRecord(payload) ? payload : {};
  const baseUrl = normalizeTrueconfBaseUrl(requestPayload.baseUrl || requestPayload.url || '');
  if (!baseUrl) {
    return {
      ok: false,
      error: 'TRUECONF_URL_INVALID'
    };
  }
  const authUrl = buildTrueconfAuthUrl(baseUrl);
  if (!authUrl) {
    return {
      ok: false,
      error: 'TRUECONF_URL_INVALID'
    };
  }

  if (trueconfAuthWindow && !trueconfAuthWindow.isDestroyed()) {
    revealExternalAuthWindow(trueconfAuthWindow);
    return {
      ok: true,
      reused: true,
      url: authUrl
    };
  }

  const senderWindow = event?.sender ? BrowserWindow.fromWebContents(event.sender) : null;
  const parentWindow = (senderWindow && !senderWindow.isDestroyed())
    ? senderWindow
    : (mainWindow && !mainWindow.isDestroyed() ? mainWindow : null);

  try {
    trueconfAuthWindow = new BrowserWindow({
      width: 1240,
      height: 900,
      minWidth: 960,
      minHeight: 680,
      parent: parentWindow || undefined,
      show: false,
      autoHideMenuBar: true,
      backgroundColor: '#ffffff',
      webPreferences: {
        sandbox: false,
        contextIsolation: true,
        partition: YUCHAT_SESSION_PARTITION,
        additionalArguments: ['--yu-window-role=trueconf-auth']
      }
    });
    bindExternalAuthWindowDiagnostics(trueconfAuthWindow, {
      providerName: 'TrueConf',
      url: authUrl
    });
    trueconfAuthWindow.setTitle('TrueConf: Авторизация');
    const revealTrueconfAuthWindow = () => {
      if (!trueconfAuthWindow || trueconfAuthWindow.isDestroyed()) return;
      revealExternalAuthWindow(trueconfAuthWindow);
    };
    trueconfAuthWindow.once('ready-to-show', revealTrueconfAuthWindow);
    trueconfAuthWindow.webContents.once('did-finish-load', revealTrueconfAuthWindow);
    trueconfAuthWindow.on('closed', () => {
      trueconfAuthWindow = null;
    });
    await trueconfAuthWindow.loadURL(authUrl);
    revealTrueconfAuthWindow();
    return {
      ok: true,
      reused: false,
      url: authUrl
    };
  } catch (error) {
    if (trueconfAuthWindow && !trueconfAuthWindow.isDestroyed()) {
      trueconfAuthWindow.destroy();
    }
    trueconfAuthWindow = null;
    return {
      ok: false,
      error: trimText(error?.message || 'TRUECONF_AUTH_WINDOW_FAILED', 220)
    };
  }
}

async function fetchCorporatePortalResource(event = null, payload = {}) {
  const requestPayload = isPlainRecord(payload) ? payload : {};
  const requestUrl = normalizeCorporatePortalFetchUrl(requestPayload.url || '');
  if (!requestUrl) {
    return {
      ok: false,
      status: 0,
      url: '',
      text: '',
      error: 'CORPORATE_PORTAL_URL_NOT_ALLOWED'
    };
  }

  const requestedMethod = String(requestPayload.method || 'GET').trim().toUpperCase();
  const method = requestedMethod === 'HEAD' ? 'HEAD' : 'GET';
  const readBody = method !== 'HEAD' && requestPayload.readBody !== false;
  const timeoutMs = Math.max(800, Math.min(15000, Number(requestPayload.timeoutMs) || 4500));
  const maxTextLength = Math.max(
    0,
    Math.min(CORPORATE_PORTAL_FETCH_MAX_TEXT_LENGTH, Number(requestPayload.maxTextLength) || CORPORATE_PORTAL_FETCH_MAX_TEXT_LENGTH)
  );

  try {
    const targetSession = getPreferredFetchSession(event) || getPersistentYuchatSession();
    const response = await fetchWithResolvedSession(targetSession, requestUrl, {
      method,
      timeoutMs,
      timeoutMessage: `Не удалось дождаться ответа корпоративного портала за ${Math.ceil(timeoutMs / 1000)} сек.`,
      headers: {
        Accept: 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8'
      },
      redirect: 'follow'
    });
    const text = readBody
      ? trimText(await response.text(), maxTextLength)
      : '';
    return {
      ok: Boolean(response.ok),
      status: Number(response.status || 0),
      url: normalizeCorporatePortalFetchUrl(response.url || requestUrl) || requestUrl,
      text
    };
  } catch (error) {
    return {
      ok: false,
      status: 0,
      url: requestUrl,
      text: '',
      error: trimText(error?.message || 'CORPORATE_PORTAL_FETCH_FAILED', 220)
    };
  }
}

async function downloadFileWithPreferredSession(event = null, urls = [], destination = '') {
  const targetPath = String(destination || '').trim();
  const attempts = Array.from(new Set(
    (Array.isArray(urls) ? urls : [urls])
      .map((value) => String(value || '').trim())
      .filter(Boolean)
  ));
  if (!targetPath || !attempts.length) {
    throw new Error('Не указан источник загрузки Vosk.');
  }

  let lastError = null;
  for (const currentUrl of attempts) {
    const controller = typeof AbortController === 'function'
      ? new AbortController()
      : null;
    let stopConnectTimer = () => {};
    let stopIdleTimer = () => {};
    const resetIdleTimer = () => {
      stopIdleTimer();
      stopIdleTimer = startAbortTimer(
        controller,
        VOSK_DOWNLOAD_IDLE_TIMEOUT_MS,
        `Не удалось скачать данные Vosk: загрузка остановилась и не присылает данные дольше ${Math.ceil(VOSK_DOWNLOAD_IDLE_TIMEOUT_MS / 1000)} сек.`
      );
    };
    try {
      stopConnectTimer = startAbortTimer(
        controller,
        VOSK_DOWNLOAD_CONNECT_TIMEOUT_MS,
        `Не удалось начать загрузку Vosk за ${Math.ceil(VOSK_DOWNLOAD_CONNECT_TIMEOUT_MS / 1000)} сек.`
      );
      const response = await fetchWithPreferredSession(event, currentUrl, {
        signal: controller?.signal
      });
      stopConnectTimer();
      if (!response.ok) {
        throw new Error(`HTTP ${response.status}`);
      }
      ensureDirSync(path.dirname(targetPath));
      const fileStream = fs.createWriteStream(targetPath);
      const completion = new Promise((resolve, reject) => {
        fileStream.on('finish', resolve);
        fileStream.on('error', reject);
      });
      try {
        const reader = response.body && typeof response.body.getReader === 'function'
          ? response.body.getReader()
          : null;
        if (reader) {
          resetIdleTimer();
          while (true) {
            let nextChunk = null;
            try {
              nextChunk = await reader.read();
            } catch (error) {
              throw resolveVoskAbortError(
                error,
                controller,
                `Не удалось скачать данные Vosk: загрузка остановилась и не присылает данные дольше ${Math.ceil(VOSK_DOWNLOAD_IDLE_TIMEOUT_MS / 1000)} сек.`
              );
            }
            const { done, value } = nextChunk || {};
            stopIdleTimer();
            if (done) break;
            if (!value) {
              resetIdleTimer();
              continue;
            }
            const chunk = value instanceof Uint8Array ? Buffer.from(value) : Buffer.from(value || []);
            if (!chunk.length) {
              resetIdleTimer();
              continue;
            }
            await new Promise((resolve, reject) => {
              fileStream.write(chunk, (error) => {
                if (error) {
                  reject(error);
                  return;
                }
                resolve();
              });
            });
            resetIdleTimer();
          }
          fileStream.end();
        } else {
          stopIdleTimer = startAbortTimer(
            controller,
            VOSK_DOWNLOAD_IDLE_TIMEOUT_MS,
            `Не удалось скачать данные Vosk: загрузка остановилась и не присылает данные дольше ${Math.ceil(VOSK_DOWNLOAD_IDLE_TIMEOUT_MS / 1000)} сек.`
          );
          try {
            fileStream.end(Buffer.from(await response.arrayBuffer()));
          } catch (error) {
            throw resolveVoskAbortError(
              error,
              controller,
              `Не удалось скачать данные Vosk: загрузка остановилась и не присылает данные дольше ${Math.ceil(VOSK_DOWNLOAD_IDLE_TIMEOUT_MS / 1000)} сек.`
            );
          } finally {
            stopIdleTimer();
          }
        }
        await completion;
        return {
          ok: true,
          url: currentUrl,
          destination: targetPath
        };
      } catch (error) {
        try {
          fileStream.destroy();
        } catch {
          // ignore file stream cleanup failures
        }
        throw resolveVoskAbortError(error, controller, 'Не удалось скачать данные Vosk.');
      } finally {
        stopIdleTimer();
      }
    } catch (error) {
      lastError = resolveVoskAbortError(error, controller, 'Не удалось скачать данные Vosk.');
      try {
        fs.unlinkSync(targetPath);
      } catch {
        // ignore failed partial cleanup
      }
      runtimeWarn('[YuChat] Vosk download attempt failed:', currentUrl, lastError);
    } finally {
      stopConnectTimer();
      stopIdleTimer();
    }
  }

  throw new Error(String(lastError?.message || 'Не удалось скачать данные Vosk.'));
}

function trimMultilineText(value = '', maxLength = 8000) {
  return String(value || '').trim().slice(0, Math.max(120, Number(maxLength) || 8000));
}

async function getVoskPythonRuntimeInfo() {
  const { stdout } = await runChildProcess(getVoskPythonBinary(), [
    '-c',
    [
      'import json',
      'import platform',
      'import sys',
      'import sysconfig',
      'print(json.dumps({',
      '  "platform": sys.platform,',
      '  "machine": platform.machine().lower(),',
      '  "sysconfigPlatform": sysconfig.get_platform().lower(),',
      '  "pythonTag": f"cp{sys.version_info[0]}{sys.version_info[1]}",',
      '  "abiTag": f"cp{sys.version_info[0]}{sys.version_info[1]}-cp{sys.version_info[0]}{sys.version_info[1]}"',
      '}))'
    ].join('\n')
  ], {
    env: {
      PYTHONNOUSERSITE: '1'
    }
  });
  return JSON.parse(String(stdout || '').trim() || '{}');
}

function selectPurePythonWheel(urls = []) {
  return (Array.isArray(urls) ? urls : []).find((entry) => {
    const filename = String(entry?.filename || '');
    return entry?.packagetype === 'bdist_wheel'
      && /\.whl$/iu.test(filename)
      && /(py3-none-any|py2\.py3-none-any)/iu.test(filename);
  }) || null;
}

function selectCffiWheel(urls = [], runtimeInfo = {}) {
  const pythonTag = String(runtimeInfo?.pythonTag || '').trim().toLowerCase();
  const abiTag = String(runtimeInfo?.abiTag || '').trim().toLowerCase();
  const machine = String(runtimeInfo?.machine || '').trim().toLowerCase();
  const sysconfigPlatform = String(runtimeInfo?.sysconfigPlatform || '').trim().toLowerCase();
  const candidates = (Array.isArray(urls) ? urls : []).filter((entry) => {
    const filename = String(entry?.filename || '').toLowerCase();
    return entry?.packagetype === 'bdist_wheel'
      && /\.whl$/iu.test(filename)
      && filename.includes(abiTag || pythonTag);
  });
  if (!candidates.length) return null;
  if (sysconfigPlatform.includes('macosx')) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('universal2'))
      || ((machine.includes('arm64') || machine.includes('aarch64'))
        ? candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('arm64'))
        : null)
      || ((machine.includes('x86_64') || machine.includes('amd64'))
        ? candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('x86_64'))
        : null)
      || (sysconfigPlatform.includes('arm64')
        ? candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('arm64'))
        : null)
      || (sysconfigPlatform.includes('x86_64')
        ? candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('x86_64'))
        : null)
      || candidates[0];
  }
  if (sysconfigPlatform.includes('win') && sysconfigPlatform.includes('amd64')) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('win_amd64')) || candidates[0];
  }
  if (sysconfigPlatform.includes('linux') && (sysconfigPlatform.includes('aarch64') || sysconfigPlatform.includes('arm64'))) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('aarch64')) || candidates[0];
  }
  if (sysconfigPlatform.includes('linux') && sysconfigPlatform.includes('x86_64')) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('x86_64')) || candidates[0];
  }
  return candidates[0];
}

function selectVoskWheel(urls = [], runtimeInfo = {}) {
  const sysconfigPlatform = String(runtimeInfo?.sysconfigPlatform || '').trim().toLowerCase();
  const candidates = (Array.isArray(urls) ? urls : []).filter((entry) => {
    const filename = String(entry?.filename || '').toLowerCase();
    return entry?.packagetype === 'bdist_wheel' && /\.whl$/iu.test(filename);
  });
  if (!candidates.length) return null;
  if (sysconfigPlatform.includes('macosx')) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('universal2'))
      || candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('macosx'))
      || candidates[0];
  }
  if (sysconfigPlatform.includes('win') && sysconfigPlatform.includes('amd64')) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('win_amd64')) || candidates[0];
  }
  if (sysconfigPlatform.includes('linux') && (sysconfigPlatform.includes('aarch64') || sysconfigPlatform.includes('arm64'))) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('aarch64')) || candidates[0];
  }
  if (sysconfigPlatform.includes('linux') && sysconfigPlatform.includes('x86_64')) {
    return candidates.find((entry) => String(entry?.filename || '').toLowerCase().includes('x86_64')) || candidates[0];
  }
  return candidates[0];
}

function selectPyPiArtifact(urls = [], spec = {}, runtimeInfo = {}) {
  const packageName = String(spec?.name || '').trim().toLowerCase();
  if (!packageName) return null;
  if (packageName === 'pycparser') {
    return selectPurePythonWheel(urls);
  }
  if (packageName === 'cffi') {
    return selectCffiWheel(urls, runtimeInfo);
  }
  if (packageName === 'vosk') {
    return selectVoskWheel(urls, runtimeInfo);
  }
  return selectPurePythonWheel(urls);
}

async function downloadPyPiWheel(event = null, spec = {}, runtimeInfo = {}, tempDir = '') {
  const packageName = String(spec?.name || '').trim();
  const packageVersion = String(spec?.version || '').trim();
  if (!packageName || !packageVersion) {
    throw new Error('Не задан пакет Vosk для загрузки.');
  }
  const metadata = await fetchJsonWithPreferredSession(
    event,
    `https://pypi.org/pypi/${encodeURIComponent(packageName)}/${encodeURIComponent(packageVersion)}/json`
  );
  const artifact = selectPyPiArtifact(metadata?.urls || [], spec, runtimeInfo);
  if (!artifact?.url || !artifact?.filename) {
    throw new Error(`Не найден подходящий wheel для ${packageName} ${packageVersion}.`);
  }
  const targetPath = path.join(String(tempDir || '').trim(), String(artifact.filename || '').trim());
  await downloadFileWithPreferredSession(event, [artifact.url], targetPath);
  return targetPath;
}

async function extractWheelArchive(wheelPath = '', targetDir = '') {
  await runChildProcess(getVoskPythonBinary(), [
    '-c',
    [
      'import sys',
      'import zipfile',
      'from pathlib import Path',
      'archive = Path(sys.argv[1]).expanduser().resolve()',
      'target = Path(sys.argv[2]).expanduser().resolve()',
      'target.mkdir(parents=True, exist_ok=True)',
      'with zipfile.ZipFile(str(archive), "r") as wheel:',
      '    wheel.extractall(str(target))'
    ].join('\n'),
    wheelPath,
    targetDir
  ], {
    env: {
      PYTHONNOUSERSITE: '1'
    }
  });
}

async function installVoskModelArchive(archivePath = '', modelDir = '') {
  await runChildProcess(getVoskPythonBinary(), [
    '-c',
    [
      'import os',
      'import shutil',
      'import sys',
      'import zipfile',
      'from pathlib import Path',
      'archive = Path(sys.argv[1]).expanduser().resolve()',
      'model_dir = Path(sys.argv[2]).expanduser().resolve()',
      'extract_root = archive.parent / f".{model_dir.name}.extract"',
      'staging_dir = model_dir.parent / f".{model_dir.name}.tmp"',
      'def remove_path(path_obj):',
      '    if path_obj.exists():',
      '        if path_obj.is_dir() and not path_obj.is_symlink():',
      '            shutil.rmtree(path_obj, ignore_errors=True)',
      '        else:',
      '            path_obj.unlink()',
      'remove_path(extract_root)',
      'remove_path(staging_dir)',
      'extract_root.mkdir(parents=True, exist_ok=True)',
      'with zipfile.ZipFile(str(archive), "r") as model_zip:',
      '    model_zip.extractall(str(extract_root))',
      'marker = next(iter(extract_root.rglob("conf/model.conf")), None)',
      'if marker is None:',
      '    raise SystemExit("Не удалось найти модель Vosk в архиве.")',
      'extracted_model_dir = marker.parent.parent',
      'shutil.move(str(extracted_model_dir), str(staging_dir))',
      'remove_path(model_dir)',
      'os.replace(str(staging_dir), str(model_dir))',
      'remove_path(extract_root)'
    ].join('\n'),
    archivePath,
    modelDir
  ], {
    env: {
      PYTHONNOUSERSITE: '1'
    }
  });
}

async function verifyEmbeddedVoskRuntime(packagesDir = '') {
  const { stdout } = await runChildProcess(getVoskPythonBinary(), [
    '-c',
    [
      'import sys',
      'sys.path.insert(0, sys.argv[1])',
      'import cffi',
      'import pycparser',
      'import requests',
      'import srt',
      'from tqdm import tqdm',
      'import vosk',
      'print("ok")'
    ].join('; '),
    packagesDir
  ], {
    env: {
      PYTHONNOUSERSITE: '1'
    }
  });
  return String(stdout || '').trim() === 'ok';
}

async function canUseEmbeddedVoskPythonPackages(packagesDir = '') {
  const targetDir = String(packagesDir || '').trim();
  if (!targetDir) {
    return false;
  }
  try {
    return await verifyEmbeddedVoskRuntime(targetDir);
  } catch {
    return false;
  }
}

async function ensureVoskPythonPackage(event = null) {
  const packagesDir = getVoskPackagesDir();
  const packageMarkers = [
    path.join(packagesDir, 'vosk', '__init__.py'),
    path.join(packagesDir, 'cffi', '__init__.py'),
    path.join(packagesDir, 'pycparser', '__init__.py'),
    path.join(packagesDir, 'requests.py'),
    path.join(packagesDir, 'srt.py'),
    path.join(packagesDir, 'tqdm.py')
  ];
  if (packageMarkers.every((marker) => fs.existsSync(marker))) {
    if (await canUseEmbeddedVoskPythonPackages(packagesDir)) {
      return { changed: false, packagesDir };
    }
    removePathSync(packagesDir);
  }
  if (await canUseSystemVoskPythonPackages()) {
    return { changed: false, packagesDir: '' };
  }
  removePathSync(packagesDir);
  ensureDirSync(packagesDir);
  const runtimeInfo = await getVoskPythonRuntimeInfo();
  const tempDir = path.join(app.getPath('temp'), YUCHAT_STORAGE_PROFILE_NAME, 'vosk-runtime-downloads');
  ensureDirSync(tempDir);
  const wheelSpecs = [
    { name: 'pycparser', version: VOSK_PYCPARSER_PACKAGE_VERSION },
    { name: 'cffi', version: VOSK_CFFI_PACKAGE_VERSION },
    { name: 'vosk', version: VOSK_PYTHON_PACKAGE_VERSION }
  ];
  for (const wheelSpec of wheelSpecs) {
    const wheelPath = await downloadPyPiWheel(event, wheelSpec, runtimeInfo, tempDir);
    try {
      await extractWheelArchive(wheelPath, packagesDir);
    } finally {
      try {
        fs.unlinkSync(wheelPath);
      } catch {
        // ignore temporary wheel cleanup failures
      }
    }
  }
  ensureVoskStubModules(packagesDir);
  if (!await canUseEmbeddedVoskPythonPackages(packagesDir)) {
    removePathSync(packagesDir);
    throw new Error('Не удалось проверить локальный Python runtime для Vosk.');
  }
  return { changed: true, packagesDir };
}

async function ensureVoskModelDownloaded(event = null) {
  const modelMarker = path.join(getVoskModelDir(), 'conf', 'model.conf');
  if (fs.existsSync(modelMarker)) {
    return { changed: false, modelDir: getVoskModelDir() };
  }
  ensureDirSync(getVoskModelsDir());
  const tempDir = path.join(app.getPath('temp'), YUCHAT_STORAGE_PROFILE_NAME, 'vosk-model-downloads');
  ensureDirSync(tempDir);
  const archivePath = path.join(tempDir, `${VOSK_MODEL_NAME}.zip`);
  await downloadFileWithPreferredSession(event, [VOSK_MODEL_URL, ...VOSK_MODEL_FALLBACK_URLS], archivePath);
  try {
    await installVoskModelArchive(archivePath, getVoskModelDir());
  } finally {
    try {
      fs.unlinkSync(archivePath);
    } catch {
      // ignore temporary archive cleanup failures
    }
  }
  return { changed: true, modelDir: getVoskModelDir() };
}

async function ensureVoskRuntimeReady(event = null) {
  if (voskRuntimeReadyPromise) {
    return voskRuntimeReadyPromise;
  }
  voskRuntimeReadyPromise = (async () => {
    const helperPath = ensureVoskHelperRuntimeFile();
    const pythonResult = await ensureVoskPythonPackage(event);
    const modelResult = await ensureVoskModelDownloaded(event);
    return {
      ok: true,
      helperPath,
      packagesDir: pythonResult.packagesDir || '',
      modelDir: getVoskModelDir(),
      pythonInstalledNow: pythonResult.changed === true,
      modelDownloadedNow: modelResult.changed === true
    };
  })();
  try {
    return await voskRuntimeReadyPromise;
  } catch (error) {
    voskRuntimeReadyPromise = null;
    throw error;
  }
}

function describeVoskPrepareError(error) {
  const message = String(error?.message || '').trim();
  const fallback = 'Не удалось подготовить офлайн-распознавание.';
  const normalized = message || fallback;
  if (/не найден исполняемый файл python3|Could not find a version|Temporary failure|Name or service not known|SSL|CERTIFICATE|Connection|timed out|ENOTFOUND|download|метаданн|wheel|скачать|загрузк|архитектур|architecture|ETIMEDOUT/iu.test(normalized)) {
    return `${normalized} Для первого запуска Vosk нужны Python 3 и доступ в интернет, чтобы скачать локальную модель и runtime распознавания.`;
  }
  return normalized;
}

async function prepareVoskDictation(event = null) {
  try {
    const runtime = await ensureVoskRuntimeReady(event);
    return {
      ok: true,
      runtime
    };
  } catch (error) {
    runtimeWarn('[YuChat] Vosk prepare failed:', error);
    return {
      ok: false,
      error: describeVoskPrepareError(error)
    };
  }
}

async function transcribeVoskDictation(event = null, payload = {}) {
  const wavBase64 = String(payload?.wavBase64 || '').trim();
  if (!wavBase64) {
    return { ok: false, error: 'Нет аудио для распознавания.' };
  }
  const transferId = trimText(payload?.transferId || '', 180);
  const abortController = transferId ? new AbortController() : null;
  if (abortController) {
    registerTransferAbortHandler(transferId, (reason = 'canceled') => {
      abortController.abort(createTransferAbortError(reason));
    });
  }
  try {
    const runtime = await ensureVoskRuntimeReady(event);
    const tempDir = path.join(app.getPath('temp'), YUCHAT_STORAGE_PROFILE_NAME, 'vosk-dictation');
    ensureDirSync(tempDir);
    const tempPath = path.join(
      tempDir,
      `dictation-${Date.now()}-${Math.random().toString(36).slice(2, 10)}.wav`
    );
    fs.writeFileSync(tempPath, Buffer.from(wavBase64, 'base64'));
    try {
      const { stdout } = await runChildProcess(getVoskPythonBinary(), [
        runtime.helperPath,
        'transcribe',
        '--packages-dir',
        runtime.packagesDir,
        '--model-dir',
        runtime.modelDir,
        '--audio-path',
        tempPath
      ], {
        env: {
          PYTHONNOUSERSITE: '1'
        },
        signal: abortController?.signal,
        onStdoutLine: (line) => {
          const parsedLine = parseJsonLine(line);
          if (!parsedLine || parsedLine.type !== 'progress' || !transferId) {
            return;
          }
          const progressMessage = trimText(
            String(parsedLine.message || parsedLine.detail || 'Распознаю речь офлайн'),
            220
          );
          emitRendererTransferProgress(event, {
            transferId,
            transferScope: 'transcript'
          }, {
            scope: 'transcript',
            stage: 'recognizing',
            percent: normalizeTransferPercent(parsedLine.percent),
            message: progressMessage
          });
        }
      });
      const parsed = stdout
        .split(/\r?\n/u)
        .map((line) => parseJsonLine(line))
        .filter(Boolean)
        .pop();
      if (!parsed || parsed.ok !== true) {
        return {
          ok: false,
          error: parsed?.error || 'Vosk не вернул результат распознавания.'
        };
      }
      return {
        ok: true,
        text: String(parsed.text || '').trim(),
        runtime
      };
    } finally {
      try {
        fs.unlinkSync(tempPath);
      } catch {
        // ignore temp cleanup issues
      }
    }
  } catch (error) {
    if (abortController?.signal?.aborted) {
      const abortReason = normalizeTransferAbortReason(
        abortController?.signal?.reason?.reason || abortController?.signal?.reason || 'canceled'
      );
      return {
        ok: false,
        code: 'TRANSFER_ABORTED',
        reason: abortReason,
        error: abortReason === 'paused'
          ? 'TXT поставлен на паузу.'
          : 'Подготовка TXT отменена.'
      };
    }
    runtimeWarn('[YuChat] Vosk dictation failed:', error);
    return {
      ok: false,
      error: String(error?.message || 'Не удалось выполнить офлайн-распознавание.')
    };
  } finally {
    if (transferId) {
      unregisterTransferAbortHandler(transferId);
    }
  }
}

function appendSmokeLog(message) {
  if (!smokeTestState) return;

  try {
    ensureDirSync(smokeArtifactsDir);
    fs.appendFileSync(smokeLogPath, `[${new Date().toISOString()}] ${message}\n`);
  } catch {
    // ignore smoke log failures
  }
}

function clampCollectionSize(items = [], maxEntries = 1000) {
  const max = Math.max(1, Number(maxEntries) || 1000);
  while (items.length > max) {
    items.shift();
  }
}

function trimText(value = '', maxLength = 4000) {
  return String(value || '').slice(0, Math.max(32, Number(maxLength) || 4000));
}

function normalizeTransferAbortReason(value = '') {
  return trimText(value || '', 32).toLowerCase() === 'paused' ? 'paused' : 'canceled';
}

function createTransferAbortError(reason = 'canceled') {
  const normalizedReason = normalizeTransferAbortReason(reason);
  const error = new Error(
    normalizedReason === 'paused'
      ? 'TXT поставлен на паузу.'
      : 'Подготовка TXT отменена.'
  );
  error.name = 'AbortError';
  error.code = 'TRANSFER_ABORTED';
  error.reason = normalizedReason;
  return error;
}

function normalizeOwaText(value = '', maxLength = 4000) {
  return String(value || '')
    .trim()
    .slice(0, Math.max(1, Number(maxLength) || 4000));
}

function normalizeOwaUrl(value = '', fallback = '') {
  const candidate = String(value || fallback || '').trim();
  if (!candidate) return '';
  try {
    const parsed = new URL(candidate);
    if (!/^https?:$/i.test(parsed.protocol)) return '';
    return parsed.toString();
  } catch {
    return '';
  }
}

function normalizeOwaOrigin(value = '') {
  const normalizedUrl = normalizeOwaUrl(value, '');
  if (!normalizedUrl) return '';
  try {
    return new URL(normalizedUrl).origin;
  } catch {
    return '';
  }
}

function buildDefaultOwaMailUrl(origin = '') {
  const normalizedOrigin = normalizeOwaOrigin(origin);
  return normalizedOrigin ? `${normalizedOrigin}/owa/#path=/mail` : '';
}

function deriveOwaCalendarUrl(mailUrl = '') {
  const normalizedMailUrl = normalizeOwaUrl(mailUrl, '');
  if (!normalizedMailUrl) return '';
  if (normalizedMailUrl.includes('#path=/mail')) {
    return normalizedMailUrl.replace('#path=/mail', '#path=/calendar');
  }
  return normalizedMailUrl.replace(/\/mail(?:[/?#]|$)/i, '/calendar$1');
}

function buildOwaHashFragment(pathValue = '/mail', params = {}) {
  const hashPath = String(pathValue || '/mail').trim() || '/mail';
  const pairs = Object.entries(isPlainRecord(params) ? params : {})
    .map(([key, value]) => {
      const normalizedKey = normalizeOwaText(key || '', 80);
      if (!normalizedKey) return '';
      if (value === undefined || value === null || value === '') return '';
      return `${encodeURIComponent(normalizedKey)}=${encodeURIComponent(String(value))}`;
    })
    .filter(Boolean);
  return `path=${hashPath}${pairs.length ? `&${pairs.join('&')}` : ''}`;
}

function buildOwaUrlWithHash(mailUrl = '', pathValue = '/mail', params = {}) {
  const normalizedMailUrl = normalizeOwaUrl(mailUrl, '');
  if (!normalizedMailUrl) return '';
  try {
    const parsed = new URL(normalizedMailUrl);
    if (!/\/owa\/?$/i.test(parsed.pathname || '')) {
      parsed.pathname = '/owa/';
    }
    parsed.search = '';
    parsed.hash = buildOwaHashFragment(pathValue, params);
    return parsed.toString();
  } catch {
    return '';
  }
}

function formatOwaLocalDateTime(timestamp = 0, options = {}) {
  const date = new Date(Number(timestamp) || Date.now());
  if (Number.isNaN(date.getTime())) return '';
  const includeMilliseconds = options.includeMilliseconds === true;
  const pad = (value, width = 2) => String(Math.max(0, Number(value) || 0)).padStart(width, '0');
  const base = [
    `${date.getFullYear()}`,
    pad(date.getMonth() + 1),
    pad(date.getDate())
  ].join('-');
  const time = [
    pad(date.getHours()),
    pad(date.getMinutes()),
    pad(date.getSeconds())
  ].join(':');
  return `${base}T${time}${includeMilliseconds ? `.${pad(date.getMilliseconds(), 3)}` : ''}`;
}

function formatOwaOffsetDateTime(timestamp = 0) {
  const date = new Date(Number(timestamp) || Date.now());
  if (Number.isNaN(date.getTime())) return '';
  const pad = (value, width = 2) => String(Math.max(0, Number(value) || 0)).padStart(width, '0');
  const base = [
    `${date.getFullYear()}`,
    pad(date.getMonth() + 1),
    pad(date.getDate())
  ].join('-');
  const time = [
    pad(date.getHours()),
    pad(date.getMinutes()),
    pad(date.getSeconds())
  ].join(':');
  const offsetMinutes = -date.getTimezoneOffset();
  const offsetSign = offsetMinutes >= 0 ? '+' : '-';
  const absoluteOffsetMinutes = Math.abs(offsetMinutes);
  const offsetHours = Math.floor(absoluteOffsetMinutes / 60);
  const remainderMinutes = absoluteOffsetMinutes % 60;
  return `${base}T${time}${offsetSign}${pad(offsetHours)}:${pad(remainderMinutes)}`;
}

function normalizeOwaSessionState(source = null, origin = '') {
  const input = isPlainRecord(source) ? source : {};
  const normalizedOrigin = normalizeOwaOrigin(origin || input.origin || input.mailUrl || '');
  return {
    origin: normalizedOrigin,
    canary: normalizeOwaText(input.canary || '', 1024),
    clientBuildVersion: normalizeOwaText(input.clientBuildVersion || '', 64),
    requestServerVersion: normalizeOwaText(input.requestServerVersion || '', 64),
    timeZoneId: normalizeOwaText(input.timeZoneId || '', 160),
    calendarFolderId: normalizeOwaText(input.calendarFolderId || '', 4096),
    calendarFolderChangeKey: normalizeOwaText(input.calendarFolderChangeKey || '', 1024),
    calendarFolderName: normalizeOwaText(input.calendarFolderName || '', 240),
    preferredClientCertificateFingerprint: normalizeOwaText(input.preferredClientCertificateFingerprint || '', 256),
    preferredClientCertificateSubjectName: normalizeOwaText(input.preferredClientCertificateSubjectName || '', 256),
    lastKnownMailUrl: normalizeOwaUrl(input.lastKnownMailUrl || buildDefaultOwaMailUrl(normalizedOrigin), ''),
    updatedAt: Math.max(0, Number(input.updatedAt || 0) || 0)
  };
}

function buildOwaSessionStateStorePath(origin = '') {
  const normalizedOrigin = normalizeOwaOrigin(origin);
  const encodedOrigin = encodeAuthStateOriginKey(normalizedOrigin);
  return encodedOrigin ? `owaOriginsByKey.${encodedOrigin}` : '';
}

function getStoredOwaSessionState(origin = '') {
  const normalizedOrigin = normalizeOwaOrigin(origin);
  if (!normalizedOrigin) return normalizeOwaSessionState({}, '');
  const storePath = buildOwaSessionStateStorePath(normalizedOrigin);
  if (!storePath) {
    return normalizeOwaSessionState({}, normalizedOrigin);
  }
  return normalizeOwaSessionState(authStateStore.get(storePath) || {}, normalizedOrigin);
}

function setStoredOwaSessionState(origin = '', patch = {}) {
  const normalizedOrigin = normalizeOwaOrigin(origin || patch?.origin || patch?.lastKnownMailUrl || '');
  if (!normalizedOrigin) return normalizeOwaSessionState({}, '');
  const currentState = getStoredOwaSessionState(normalizedOrigin);
  const nextState = normalizeOwaSessionState({
    ...currentState,
    ...(isPlainRecord(patch) ? patch : {}),
    origin: normalizedOrigin,
    updatedAt: Date.now()
  }, normalizedOrigin);
  const storePath = buildOwaSessionStateStorePath(normalizedOrigin);
  if (storePath) {
    authStateStore.set(storePath, nextState);
  }
  return nextState;
}

function emitOwaSessionReadyEvent(origin = '', previousState = null, nextState = null) {
  const normalizedOrigin = normalizeOwaOrigin(origin || nextState?.origin || '');
  const previousCanary = normalizeOwaText(previousState?.canary || '', 1024);
  const nextCanary = normalizeOwaText(nextState?.canary || '', 1024);
  if (!normalizedOrigin || !mainWindow || mainWindow.isDestroyed()) {
    return false;
  }
  if (!nextCanary || (previousCanary && previousCanary === nextCanary)) {
    return false;
  }
  try {
    mainWindow.webContents.send('yuchat-calendar-session-ready', {
      origin: normalizedOrigin,
      ready: true,
      updatedAt: Math.max(0, Number(nextState?.updatedAt || Date.now()) || Date.now())
    });
    return true;
  } catch {
    return false;
  }
}

function findOwaWindowByWebContents(targetWebContents = null) {
  if (!targetWebContents) return null;
  for (const candidateWindow of owaWindowsByOrigin.values()) {
    if (
      candidateWindow instanceof BrowserWindow
      && !candidateWindow.isDestroyed()
      && candidateWindow.webContents === targetWebContents
    ) {
      return candidateWindow;
    }
  }
  return null;
}

function resolveOwaPromptOwnerWindow(targetWebContents = null) {
  const owaWindow = findOwaWindowByWebContents(targetWebContents);
  if (owaWindow && !owaWindow.isDestroyed() && owaWindow.isVisible()) {
    return owaWindow;
  }
  const ownerWindow = getDialogOwnerWindow();
  if (ownerWindow && !ownerWindow.isDestroyed() && ownerWindow.isVisible()) {
    return ownerWindow;
  }
  return undefined;
}

function clearOwaAutoRevealTimer(owaWindow = null) {
  const timer = Number(owaWindow?.__yuOwaAutoRevealTimer || 0);
  if (!timer) return;
  clearTimeout(timer);
  owaWindow.__yuOwaAutoRevealTimer = 0;
}

function revealOwaWindow(owaWindow = null) {
  if (!(owaWindow instanceof BrowserWindow) || owaWindow.isDestroyed()) {
    return false;
  }
  clearOwaAutoRevealTimer(owaWindow);
  owaWindow.__yuOwaBackgroundConnect = false;
  if (owaWindow.isMinimized()) {
    owaWindow.restore();
  }
  if (!owaWindow.isVisible()) {
    owaWindow.show();
  }
  owaWindow.focus();
  return true;
}

function scheduleOwaAutoReveal(owaWindow = null, origin = '', delayMs = OWA_AUTO_CONNECT_REVEAL_DELAY_MS) {
  if (!(owaWindow instanceof BrowserWindow) || owaWindow.isDestroyed()) {
    return;
  }
  clearOwaAutoRevealTimer(owaWindow);
  if (owaWindow.__yuOwaBackgroundConnect !== true || owaWindow.isVisible()) {
    return;
  }
  owaWindow.__yuOwaAutoRevealTimer = setTimeout(() => {
    owaWindow.__yuOwaAutoRevealTimer = 0;
    if (!(owaWindow instanceof BrowserWindow) || owaWindow.isDestroyed()) {
      return;
    }
    const sessionState = getStoredOwaSessionState(origin);
    if (sessionState.canary) {
      return;
    }
    revealOwaWindow(owaWindow);
  }, Math.max(1200, Number(delayMs || OWA_AUTO_CONNECT_REVEAL_DELAY_MS) || OWA_AUTO_CONNECT_REVEAL_DELAY_MS));
}

function isOwaInteractiveAuthUrl(targetUrl = '') {
  const normalizedUrl = normalizeOwaUrl(targetUrl, '');
  if (!normalizedUrl) return false;
  return /(?:\/owa\/auth\/|\/adfs\/|\/auth\/|\/login\b|\/logon\b|\/signin\b|sso|oauth|federation)/iu.test(normalizedUrl);
}

function maybeRevealOwaWindowForInteractiveAuth(owaWindow = null, origin = '', targetUrl = '') {
  if (!(owaWindow instanceof BrowserWindow) || owaWindow.isDestroyed()) {
    return false;
  }
  if (owaWindow.__yuOwaBackgroundConnect !== true || owaWindow.isVisible()) {
    return false;
  }
  if (getStoredOwaSessionState(origin).canary) {
    clearOwaAutoRevealTimer(owaWindow);
    return false;
  }
  if (!isOwaInteractiveAuthUrl(targetUrl)) {
    return false;
  }
  return revealOwaWindow(owaWindow);
}

function formatOwaCertificateDate(value = 0) {
  const seconds = Math.max(0, Number(value || 0) || 0);
  if (!seconds) return '';
  try {
    return new Date(seconds * 1000).toLocaleDateString('ru-RU');
  } catch {
    return '';
  }
}

function buildOwaPromptDataUrl(html = '') {
  return `data:text/html;charset=UTF-8,${encodeURIComponent(String(html || ''))}`;
}

function createOwaPromptWindow(options = {}) {
  const ownerWindow = resolveOwaPromptOwnerWindow(options.webContents || null);
  return new BrowserWindow({
    parent: ownerWindow,
    modal: Boolean(ownerWindow),
    width: Math.max(420, Number(options.width || OWA_PROMPT_WINDOW_WIDTH) || OWA_PROMPT_WINDOW_WIDTH),
    height: Math.max(300, Number(options.height || OWA_PROMPT_WINDOW_HEIGHT) || OWA_PROMPT_WINDOW_HEIGHT),
    show: false,
    resizable: false,
    minimizable: false,
    maximizable: false,
    fullscreenable: false,
    autoHideMenuBar: true,
    backgroundColor: '#f4f7fb',
    title: normalizeOwaText(options.title || 'Подключение OWA', 80) || 'Подключение OWA',
    webPreferences: {
      sandbox: false,
      contextIsolation: false,
      nodeIntegration: true
    }
  });
}

function showOwaBasicAuthPrompt(details = {}, authInfo = {}, options = {}) {
  const promptChannel = `owa-basic-auth:${Date.now().toString(36)}:${Math.random().toString(16).slice(2, 8)}`;
  const resolvedHost = (() => {
    const directHost = normalizeOwaText(authInfo?.host || '', 240);
    if (directHost) return directHost;
    try {
      return normalizeOwaText(new URL(details?.url || 'https://owa.invalid').host || '', 240);
    } catch {
      return '';
    }
  })();
  const realm = normalizeOwaText(authInfo?.realm || '', 240);
  const scheme = normalizeOwaText(authInfo?.scheme || 'Basic', 64);
  const promptWindow = createOwaPromptWindow({
    title: 'Вход в OWA',
    width: 520,
    height: 360,
    webContents: options.webContents || null
  });
  const hintParts = [
    authInfo?.isProxy === true ? 'Прокси-сервер' : 'Сервер OWA',
    resolvedHost || normalizeOwaText(details?.url || '', 320),
    realm ? `область: ${realm}` : '',
    scheme ? `схема: ${scheme}` : ''
  ].filter(Boolean);
  const promptHtml = `<!doctype html>
<html lang="ru">
<head>
  <meta charset="utf-8" />
  <title>Вход в OWA</title>
  <style>
    :root { color-scheme: light; }
    body {
      margin: 0;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      background: #eef3f8;
      color: #142235;
    }
    .shell {
      min-height: 100vh;
      padding: 24px;
      box-sizing: border-box;
      display: flex;
      align-items: center;
      justify-content: center;
    }
    .card {
      width: 100%;
      background: #ffffff;
      border-radius: 18px;
      padding: 22px;
      box-shadow: 0 18px 60px rgba(20, 34, 53, 0.16);
    }
    h1 {
      margin: 0 0 8px;
      font-size: 24px;
      line-height: 1.2;
    }
    p {
      margin: 0 0 18px;
      color: #49617d;
      line-height: 1.5;
    }
    .hint {
      margin-bottom: 18px;
      padding: 12px 14px;
      border-radius: 12px;
      background: #f3f7fb;
      color: #29435f;
      font-size: 13px;
      line-height: 1.45;
    }
    label {
      display: block;
      margin-bottom: 12px;
      font-size: 13px;
      color: #36506c;
    }
    input {
      width: 100%;
      margin-top: 6px;
      padding: 11px 12px;
      border: 1px solid #c7d4e3;
      border-radius: 11px;
      font-size: 15px;
      box-sizing: border-box;
      outline: none;
    }
    input:focus {
      border-color: #3d7df0;
      box-shadow: 0 0 0 4px rgba(61, 125, 240, 0.12);
    }
    .actions {
      display: flex;
      justify-content: flex-end;
      gap: 10px;
      margin-top: 18px;
    }
    button {
      border: 0;
      border-radius: 11px;
      padding: 11px 16px;
      font-size: 14px;
      cursor: pointer;
    }
    .cancel {
      background: #e7edf4;
      color: #29435f;
    }
    .submit {
      background: #1f6feb;
      color: #ffffff;
      font-weight: 600;
    }
  </style>
</head>
<body>
  <div class="shell">
    <form class="card" id="auth-form">
      <h1>Подключение к OWA</h1>
      <p>Для продолжения введите логин и пароль, которые запрашивает ваш почтовый сервер.</p>
      <div class="hint">${escapeHtml(hintParts.join(' · '))}</div>
      <label>Логин
        <input id="username" name="username" type="text" autocomplete="username" />
      </label>
      <label>Пароль
        <input id="password" name="password" type="password" autocomplete="current-password" />
      </label>
      <div class="actions">
        <button class="cancel" type="button" id="cancel">Отмена</button>
        <button class="submit" type="submit">Продолжить</button>
      </div>
    </form>
  </div>
  <script>
    const { ipcRenderer } = require('electron');
    const submitChannel = ${JSON.stringify(promptChannel)};
    const form = document.getElementById('auth-form');
    const usernameInput = document.getElementById('username');
    const passwordInput = document.getElementById('password');
    const cancelButton = document.getElementById('cancel');
    cancelButton.addEventListener('click', () => window.close());
    form.addEventListener('submit', (event) => {
      event.preventDefault();
      ipcRenderer.send(submitChannel, {
        username: usernameInput.value || '',
        password: passwordInput.value || ''
      });
      window.close();
    });
    window.addEventListener('keydown', (event) => {
      if (event.key === 'Escape') {
        event.preventDefault();
        window.close();
      }
    });
    setTimeout(() => usernameInput.focus(), 40);
  </script>
</body>
</html>`;

  return new Promise((resolve) => {
    let settled = false;
    const submitListener = (_event, payload = {}) => {
      settle({
        username: normalizeOwaText(payload?.username || '', 240),
        password: String(payload?.password || '').slice(0, 2048)
      });
    };
    const settle = (result = null) => {
      if (settled) return;
      settled = true;
      ipcMain.removeListener(promptChannel, submitListener);
      if (promptWindow && !promptWindow.isDestroyed()) {
        promptWindow.close();
      }
      resolve(result && result.username ? result : null);
    };
    ipcMain.on(promptChannel, submitListener);
    promptWindow.once('ready-to-show', () => {
      if (!promptWindow.isDestroyed()) {
        promptWindow.show();
        promptWindow.focus();
      }
    });
    promptWindow.on('closed', () => {
      settle(null);
    });
    promptWindow.loadURL(buildOwaPromptDataUrl(promptHtml)).catch(() => {
      settle(null);
    });
  });
}

function showOwaClientCertificatePrompt(url = '', certificateList = [], options = {}) {
  const promptChannel = `owa-client-cert:${Date.now().toString(36)}:${Math.random().toString(16).slice(2, 8)}`;
  const promptWindow = createOwaPromptWindow({
    title: 'Сертификат OWA',
    width: 640,
    height: 500,
    webContents: options.webContents || null
  });
  const certificateMarkup = (Array.isArray(certificateList) ? certificateList : [])
    .map((certificate, index) => {
      const fingerprint = normalizeOwaText(certificate?.fingerprint || '', 256);
      const subject = normalizeOwaText(certificate?.subjectName || certificate?.subject?.commonName || `Сертификат ${index + 1}`, 240);
      const issuer = normalizeOwaText(certificate?.issuerName || certificate?.issuer?.commonName || '', 240);
      const expiry = formatOwaCertificateDate(certificate?.validExpiry || 0);
      const meta = [
        issuer ? `Выдан: ${issuer}` : '',
        expiry ? `Действует до ${expiry}` : '',
        fingerprint ? `Отпечаток: ${fingerprint.slice(-16)}` : ''
      ].filter(Boolean).join(' · ');
      return `
        <label class="option">
          <input type="radio" name="certificate" value="${escapeHtml(fingerprint)}"${index === 0 ? ' checked' : ''} />
          <span class="option-copy">
            <span class="option-title">${escapeHtml(subject)}</span>
            ${meta ? `<span class="option-meta">${escapeHtml(meta)}</span>` : ''}
          </span>
        </label>
      `;
    })
    .join('');
  const promptHtml = `<!doctype html>
<html lang="ru">
<head>
  <meta charset="utf-8" />
  <title>Сертификат OWA</title>
  <style>
    :root { color-scheme: light; }
    body {
      margin: 0;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      background: #eef3f8;
      color: #142235;
    }
    .shell {
      min-height: 100vh;
      padding: 24px;
      box-sizing: border-box;
      display: flex;
      align-items: center;
      justify-content: center;
    }
    .card {
      width: 100%;
      background: #ffffff;
      border-radius: 18px;
      padding: 22px;
      box-shadow: 0 18px 60px rgba(20, 34, 53, 0.16);
      display: flex;
      flex-direction: column;
      gap: 16px;
    }
    h1 {
      margin: 0;
      font-size: 24px;
      line-height: 1.2;
    }
    p {
      margin: 0;
      color: #49617d;
      line-height: 1.5;
    }
    .hint {
      padding: 12px 14px;
      border-radius: 12px;
      background: #f3f7fb;
      color: #29435f;
      font-size: 13px;
      line-height: 1.45;
    }
    .list {
      display: flex;
      flex-direction: column;
      gap: 10px;
      max-height: 250px;
      overflow: auto;
      padding-right: 4px;
    }
    .option {
      display: flex;
      gap: 12px;
      align-items: flex-start;
      padding: 12px 14px;
      border-radius: 12px;
      border: 1px solid #d6e0eb;
      background: #fbfdff;
      cursor: pointer;
    }
    .option-copy {
      display: flex;
      flex-direction: column;
      gap: 4px;
    }
    .option-title {
      font-size: 14px;
      font-weight: 600;
      color: #17324f;
    }
    .option-meta {
      font-size: 12px;
      color: #5c738d;
      line-height: 1.4;
    }
    .actions {
      display: flex;
      justify-content: flex-end;
      gap: 10px;
    }
    button {
      border: 0;
      border-radius: 11px;
      padding: 11px 16px;
      font-size: 14px;
      cursor: pointer;
    }
    .cancel {
      background: #e7edf4;
      color: #29435f;
    }
    .submit {
      background: #1f6feb;
      color: #ffffff;
      font-weight: 600;
    }
  </style>
</head>
<body>
  <div class="shell">
    <form class="card" id="cert-form">
      <div>
        <h1>Выбор сертификата</h1>
        <p>Для подключения к OWA выберите клиентский сертификат, который должен использоваться для этого адреса.</p>
      </div>
      <div class="hint">${escapeHtml(normalizeOwaText(url || '', 320))}</div>
      <div class="list">${certificateMarkup}</div>
      <div class="actions">
        <button class="cancel" type="button" id="cancel">Отмена</button>
        <button class="submit" type="submit">Продолжить</button>
      </div>
    </form>
  </div>
  <script>
    const { ipcRenderer } = require('electron');
    const submitChannel = ${JSON.stringify(promptChannel)};
    const form = document.getElementById('cert-form');
    const cancelButton = document.getElementById('cancel');
    cancelButton.addEventListener('click', () => window.close());
    form.addEventListener('submit', (event) => {
      event.preventDefault();
      const selected = document.querySelector('input[name="certificate"]:checked');
      ipcRenderer.send(submitChannel, {
        fingerprint: selected ? selected.value : ''
      });
      window.close();
    });
    window.addEventListener('keydown', (event) => {
      if (event.key === 'Escape') {
        event.preventDefault();
        window.close();
      }
    });
  </script>
</body>
</html>`;

  return new Promise((resolve) => {
    let settled = false;
    const submitListener = (_event, payload = {}) => {
      settle(normalizeOwaText(payload?.fingerprint || '', 256));
    };
    const settle = (fingerprint = '') => {
      if (settled) return;
      settled = true;
      ipcMain.removeListener(promptChannel, submitListener);
      if (promptWindow && !promptWindow.isDestroyed()) {
        promptWindow.close();
      }
      resolve(fingerprint || '');
    };
    ipcMain.on(promptChannel, submitListener);
    promptWindow.once('ready-to-show', () => {
      if (!promptWindow.isDestroyed()) {
        promptWindow.show();
        promptWindow.focus();
      }
    });
    promptWindow.on('closed', () => {
      settle('');
    });
    promptWindow.loadURL(buildOwaPromptDataUrl(promptHtml)).catch(() => {
      settle('');
    });
  });
}

function isOwaRequestContext(targetUrl = '', targetWebContents = null) {
  if (findOwaWindowByWebContents(targetWebContents)) {
    return true;
  }
  const origin = normalizeOwaOrigin(targetUrl);
  if (!origin) return false;
  if (getStoredOwaSessionState(origin).origin) {
    return true;
  }
  return /\/owa(?:[/?#]|$)/iu.test(String(targetUrl || ''));
}

function buildOwaBasicAuthPromptKey(details = {}, authInfo = {}) {
  return [
    normalizeOwaOrigin(details?.url || ''),
    authInfo?.isProxy === true ? 'proxy' : 'server',
    normalizeOwaText(authInfo?.host || '', 240).toLowerCase(),
    Math.max(0, Number(authInfo?.port || 0) || 0),
    normalizeOwaText(authInfo?.realm || '', 240),
    normalizeOwaText(authInfo?.scheme || '', 64).toLowerCase()
  ].join('\u001f');
}

async function promptOwaBasicAuthCredentials(details = {}, authInfo = {}, targetWebContents = null) {
  const promptKey = buildOwaBasicAuthPromptKey(details, authInfo);
  let pendingPrompt = owaPendingBasicAuthPromptByKey.get(promptKey) || null;
  if (!pendingPrompt) {
    pendingPrompt = showOwaBasicAuthPrompt(details, authInfo, {
      webContents: targetWebContents
    }).finally(() => {
      owaPendingBasicAuthPromptByKey.delete(promptKey);
    });
    owaPendingBasicAuthPromptByKey.set(promptKey, pendingPrompt);
  }
  return pendingPrompt.catch(() => null);
}

async function selectOwaClientCertificate(url = '', certificateList = [], targetWebContents = null) {
  const certificates = Array.isArray(certificateList) ? certificateList.filter(Boolean) : [];
  if (!certificates.length) {
    return null;
  }
  const origin = normalizeOwaOrigin(url);
  const currentState = getStoredOwaSessionState(origin);
  const preferredFingerprint = normalizeOwaText(currentState.preferredClientCertificateFingerprint || '', 256);
  if (preferredFingerprint) {
    const preferredCertificate = certificates.find((certificate) => (
      normalizeOwaText(certificate?.fingerprint || '', 256) === preferredFingerprint
    )) || null;
    if (preferredCertificate) {
      return preferredCertificate;
    }
  }
  if (certificates.length === 1) {
    const onlyCertificate = certificates[0];
    if (origin) {
      setStoredOwaSessionState(origin, {
        preferredClientCertificateFingerprint: normalizeOwaText(onlyCertificate?.fingerprint || '', 256),
        preferredClientCertificateSubjectName: normalizeOwaText(onlyCertificate?.subjectName || '', 256)
      });
    }
    return onlyCertificate;
  }
  const promptKey = origin || normalizeOwaText(url || '', 1024);
  let pendingPrompt = owaPendingCertificatePromptByKey.get(promptKey) || null;
  if (!pendingPrompt) {
    pendingPrompt = showOwaClientCertificatePrompt(url, certificates, {
      webContents: targetWebContents
    }).finally(() => {
      owaPendingCertificatePromptByKey.delete(promptKey);
    });
    owaPendingCertificatePromptByKey.set(promptKey, pendingPrompt);
  }
  const selectedFingerprint = await pendingPrompt.catch(() => '');
  if (!selectedFingerprint) {
    return null;
  }
  const selectedCertificate = certificates.find((certificate) => (
    normalizeOwaText(certificate?.fingerprint || '', 256) === selectedFingerprint
  )) || null;
  if (selectedCertificate && origin) {
    setStoredOwaSessionState(origin, {
      preferredClientCertificateFingerprint: normalizeOwaText(selectedCertificate?.fingerprint || '', 256),
      preferredClientCertificateSubjectName: normalizeOwaText(selectedCertificate?.subjectName || '', 256)
    });
  }
  return selectedCertificate;
}

function getRequestHeaderValue(requestHeaders = [], headerName = '') {
  const targetName = String(headerName || '').trim().toLowerCase();
  if (!targetName) return '';
  if (Array.isArray(requestHeaders)) {
    const match = requestHeaders.find((entry) => String(entry?.name || '').trim().toLowerCase() === targetName) || null;
    return normalizeOwaText(match?.value || '', 8192);
  }
  if (isPlainRecord(requestHeaders)) {
    const matchedKey = Object.keys(requestHeaders).find((key) => String(key || '').trim().toLowerCase() === targetName) || '';
    const rawValue = matchedKey ? requestHeaders[matchedKey] : '';
    const value = Array.isArray(rawValue) ? rawValue.find(Boolean) || '' : rawValue;
    return normalizeOwaText(value || '', 8192);
  }
  return '';
}

function decodeOwaUrlPostData(requestHeaders = []) {
  const encoded = getRequestHeaderValue(requestHeaders, 'x-owa-urlpostdata');
  if (!encoded) return null;
  try {
    const decoded = decodeURIComponent(encoded);
    const parsed = JSON.parse(decoded);
    return isPlainRecord(parsed) ? parsed : null;
  } catch {
    return null;
  }
}

function extractOwaFolderDescriptor(source = null) {
  const descriptor = isPlainRecord(source) ? source : {};
  const folderRecord = (
    (isPlainRecord(descriptor.CalendarId) && descriptor.CalendarId)
    || (isPlainRecord(descriptor.BaseFolderId) && descriptor.BaseFolderId)
    || (isPlainRecord(descriptor.FolderId) && descriptor.FolderId)
    || (isPlainRecord(descriptor.Id) && descriptor.Id)
    || descriptor
  );
  const id = normalizeOwaText(folderRecord?.Id || folderRecord?.id || '', 4096);
  const changeKey = normalizeOwaText(folderRecord?.ChangeKey || folderRecord?.changeKey || '', 1024);
  const name = normalizeOwaText(
    descriptor?.Name
    || descriptor?.DisplayName
    || descriptor?.CalendarName
    || descriptor?.FolderName
    || '',
    240
  );
  return {
    id,
    changeKey,
    name
  };
}

function captureOwaSessionStateFromRequest(requestUrl = '', requestHeaders = []) {
  const origin = normalizeOwaOrigin(requestUrl);
  if (!origin) return null;
  const payload = decodeOwaUrlPostData(requestHeaders);
  const currentState = getStoredOwaSessionState(origin);
  const nextPatch = {
    canary: getRequestHeaderValue(requestHeaders, 'x-owa-canary') || currentState.canary,
    clientBuildVersion: getRequestHeaderValue(requestHeaders, 'x-owa-clientbuildversion') || currentState.clientBuildVersion,
    lastKnownMailUrl: currentState.lastKnownMailUrl || buildDefaultOwaMailUrl(origin)
  };

  if (isPlainRecord(payload?.Header)) {
    nextPatch.requestServerVersion = normalizeOwaText(
      payload.Header.RequestServerVersion || currentState.requestServerVersion,
      64
    );
    nextPatch.timeZoneId = normalizeOwaText(
      payload?.Header?.TimeZoneContext?.TimeZoneDefinition?.Id || currentState.timeZoneId,
      160
    );
  }

  const folderDescriptor = extractOwaFolderDescriptor(
    payload?.Body?.CalendarId
    || payload?.request?.subscriptionData?.[0]?.Parameters
    || payload?.request?.subscriptionData?.[0]
    || null
  );
  if (folderDescriptor.id) {
    nextPatch.calendarFolderId = folderDescriptor.id;
    nextPatch.calendarFolderChangeKey = folderDescriptor.changeKey || currentState.calendarFolderChangeKey;
    if (folderDescriptor.name) {
      nextPatch.calendarFolderName = folderDescriptor.name;
    }
  }

  const nextState = setStoredOwaSessionState(origin, nextPatch);
  emitOwaSessionReadyEvent(origin, currentState, nextState);
  return nextState;
}

function attachOwaRequestCapture(targetSession = getPersistentYuchatSession()) {
  if (!targetSession || configuredOwaCaptureSessions.has(targetSession)) {
    return targetSession;
  }
  configuredOwaCaptureSessions.add(targetSession);
  try {
    targetSession.webRequest.onBeforeSendHeaders({
      urls: ['*://*/owa/service.svc*']
    }, (details, callback) => {
      try {
        captureOwaSessionStateFromRequest(details?.url || '', details?.requestHeaders || []);
      } catch (error) {
        runtimeWarn('[YuChat][OWA] Failed to capture OWA request metadata:', error);
      }
      callback({
        requestHeaders: details.requestHeaders
      });
    });
  } catch (error) {
    runtimeWarn('[YuChat][OWA] Failed to attach request capture:', error);
  }
  return targetSession;
}

function buildOwaRequestIdentifiers() {
  owaRequestSequence += 1;
  const sequence = Math.max(1, owaRequestSequence);
  const timePart = Date.now();
  const randomPart = Math.random().toString(16).slice(2, 10).toUpperCase();
  const requestId = `${randomPart}${timePart}_${sequence}`;
  return {
    requestId,
    actionId: `-${2000 + sequence}`,
    attempt: '1'
  };
}

function buildOwaJsonRequestHeaders(sessionState = {}) {
  return {
    __type: 'JsonRequestHeaders:#Exchange',
    RequestServerVersion: normalizeOwaText(sessionState.requestServerVersion || 'V2017_08_18', 64),
    TimeZoneContext: {
      __type: 'TimeZoneContext:#Exchange',
      TimeZoneDefinition: {
        __type: 'TimeZoneDefinitionType:#Exchange',
        Id: normalizeOwaText(sessionState.timeZoneId || 'UTC', 160) || 'UTC'
      }
    }
  };
}

function buildOwaFetchHeaders(action = '', sessionState = {}, options = {}) {
  const identifiers = buildOwaRequestIdentifiers();
  const requestPayload = isPlainRecord(options.requestPayload) ? options.requestPayload : {};
  const serializedPayload = JSON.stringify(requestPayload);
  const actionName = normalizeOwaText(
    options.actionName
    || (action === 'GetCalendarView' ? 'GetCalendarViewAction_Month' : `${action}Action`),
    160
  ) || `${action}Action`;
  return {
    headers: {
      Accept: 'application/json, text/plain, */*',
      Action: action,
      'Content-Type': 'application/json; charset=UTF-8',
      'X-OWA-ActionId': identifiers.actionId,
      'X-OWA-ActionName': actionName,
      'X-OWA-Attempt': identifiers.attempt,
      'X-OWA-CANARY': sessionState.canary,
      'X-OWA-ClientBegin': new Date().toISOString().slice(0, 23),
      'X-OWA-ClientBuildVersion': sessionState.clientBuildVersion,
      'X-OWA-CorrelationId': identifiers.requestId,
      'X-OWA-UrlPostData': encodeURIComponent(serializedPayload),
      'client-request-id': identifiers.requestId
    },
    actionId: identifiers.actionId
  };
}

function buildOwaServiceUrl(origin = '', action = '', actionId = '-1') {
  const normalizedOrigin = normalizeOwaOrigin(origin);
  const normalizedAction = normalizeOwaText(action || '', 120);
  const normalizedActionId = normalizeOwaText(actionId || '-1', 32) || '-1';
  if (!normalizedOrigin || !normalizedAction) return '';
  return `${normalizedOrigin}/owa/service.svc?action=${encodeURIComponent(normalizedAction)}&EP=1&ID=${encodeURIComponent(normalizedActionId)}&AC=1`;
}

function ensureOwaReadyState(origin = '') {
  const sessionState = getStoredOwaSessionState(origin);
  if (!sessionState.origin) {
    const error = new Error('Некорректный адрес OWA.');
    error.code = 'OWA_URL_INVALID';
    throw error;
  }
  if (!sessionState.canary) {
    const error = new Error('Откройте календарь OWA и дождитесь загрузки, чтобы завершить подключение.');
    error.code = 'OWA_NOT_READY';
    throw error;
  }
  return sessionState;
}

async function readJsonResponse(response = null) {
  const rawText = await response.text().catch(() => '');
  let parsed = null;
  try {
    parsed = rawText ? JSON.parse(rawText) : null;
  } catch {
    parsed = null;
  }
  return {
    rawText,
    parsed
  };
}

async function executeOwaJsonRequest(event = null, mailUrl = '', action = '', requestPayload = {}, options = {}) {
  const normalizedMailUrl = normalizeOwaUrl(mailUrl, '');
  const origin = normalizeOwaOrigin(normalizedMailUrl);
  if (!origin || !action) {
    const error = new Error('Некорректные параметры OWA-запроса.');
    error.code = 'OWA_REQUEST_INVALID';
    throw error;
  }
  let sessionState = ensureOwaReadyState(origin);
  if (normalizedMailUrl) {
    sessionState = setStoredOwaSessionState(origin, {
      ...sessionState,
      lastKnownMailUrl: normalizedMailUrl
    });
  }
  const targetSession = getPreferredFetchSession(event) || getPersistentYuchatSession();
  attachOwaRequestCapture(targetSession);
  const { headers, actionId } = buildOwaFetchHeaders(action, sessionState, {
    actionName: options.actionName,
    requestPayload
  });
  const requestUrl = buildOwaServiceUrl(origin, action, actionId);
  const response = await fetchWithResolvedSession(targetSession, requestUrl, {
    method: 'POST',
    body: '',
    headers,
    timeoutMs: Math.max(5000, Number(options.timeoutMs || 0) || 18000),
    timeoutMessage: `Не удалось получить ответ OWA для ${action}.`
  });
  const { rawText, parsed } = await readJsonResponse(response);
  if (!response.ok) {
    const error = new Error(
      [401, 403, 440].includes(Number(response.status || 0))
        ? 'Сессия почты истекла. Откройте окно OWA и войдите снова.'
        : `OWA вернула ошибку ${response.status} для ${action}.`
    );
    error.code = [401, 403, 440].includes(Number(response.status || 0)) ? 'OWA_AUTH_REQUIRED' : 'OWA_HTTP_ERROR';
    error.status = Number(response.status || 0);
    error.responseText = rawText.slice(0, 1200);
    throw error;
  }
  if (!parsed || typeof parsed !== 'object') {
    const error = new Error(`OWA вернула неожиданный ответ для ${action}.`);
    error.code = 'OWA_PARSE_ERROR';
    error.responseText = rawText.slice(0, 1200);
    throw error;
  }
  return parsed;
}

function collectOwaCalendarFolderCandidates(response = null) {
  const safeResponse = isPlainRecord(response) ? response : {};
  const groups = Array.isArray(safeResponse.CalendarGroups) ? safeResponse.CalendarGroups : [];
  const folders = Array.isArray(safeResponse.CalendarFolders) ? safeResponse.CalendarFolders : [];
  const candidates = [];
  groups.forEach((group) => {
    const calendars = Array.isArray(group?.Calendars) ? group.Calendars : [];
    calendars.forEach((calendar) => candidates.push(calendar));
  });
  folders.forEach((folder) => candidates.push(folder));
  return candidates;
}

async function ensureOwaCalendarFolderState(event = null, mailUrl = '', options = {}) {
  const normalizedMailUrl = normalizeOwaUrl(mailUrl, '');
  const origin = normalizeOwaOrigin(normalizedMailUrl);
  if (!origin) {
    const error = new Error('Некорректный адрес OWA.');
    error.code = 'OWA_URL_INVALID';
    throw error;
  }
  const currentState = ensureOwaReadyState(origin);
  if (currentState.calendarFolderId && options.forceRefresh !== true) {
    return currentState;
  }
  const response = await executeOwaJsonRequest(event, normalizedMailUrl, 'GetCalendarFolders', {}, {
    actionName: 'GetCalendarFoldersAction',
    timeoutMs: 15000
  });
  const folderCandidates = collectOwaCalendarFolderCandidates(response);
  const selectedFolder = folderCandidates.find((item) => (
    item?.IsDefaultCalendar === true
    || item?.IsDefaultFolder === true
    || item?.IsDefault === true
  )) || folderCandidates[0] || null;
  const folderDescriptor = extractOwaFolderDescriptor(selectedFolder);
  if (!folderDescriptor.id) {
    const error = new Error('OWA не вернула основной календарь.');
    error.code = 'OWA_CALENDAR_FOLDER_MISSING';
    throw error;
  }
  return setStoredOwaSessionState(origin, {
    ...currentState,
    calendarFolderId: folderDescriptor.id,
    calendarFolderChangeKey: folderDescriptor.changeKey || currentState.calendarFolderChangeKey,
    calendarFolderName: folderDescriptor.name || currentState.calendarFolderName,
    lastKnownMailUrl: normalizedMailUrl || currentState.lastKnownMailUrl
  });
}

function extractOwaItemId(source = null) {
  const itemRecord = isPlainRecord(source) ? source : {};
  const id = normalizeOwaText(itemRecord?.Id || itemRecord?.id || '', 4096);
  const changeKey = normalizeOwaText(itemRecord?.ChangeKey || itemRecord?.changeKey || '', 1024);
  return {
    id,
    changeKey
  };
}

function parseOwaDateTimestamp(value = '') {
  const rawValue = normalizeOwaText(value || '', 128);
  if (!rawValue) return 0;
  const parsed = new Date(rawValue).getTime();
  return Number.isFinite(parsed) && parsed > 0 ? parsed : 0;
}

function extractOwaUrlCandidate(value = '') {
  const rawValue = String(value || '');
  const match = rawValue.match(/https?:\/\/[^\s"'<>]+/iu);
  return normalizeOwaUrl(match?.[0] || '', '');
}

function normalizeOwaCalendarEventType(value = '') {
  const source = String(value || '').trim().toLowerCase();
  return /focus|фокус/u.test(source) ? 'focus' : 'meeting';
}

function normalizeOwaFreeBusyType(value = '') {
  return normalizeOwaText(value || '', 48).toLowerCase();
}

function shouldTreatOwaBusyTypeAsBusy(value = '') {
  const normalized = normalizeOwaFreeBusyType(value);
  return Boolean(normalized && normalized !== 'free' && normalized !== 'workingelsewhere');
}

function extractOwaAttendees(item = null) {
  const source = isPlainRecord(item) ? item : {};
  const attendeeCollections = [
    Array.isArray(source.RequiredAttendees) ? source.RequiredAttendees : [],
    Array.isArray(source.OptionalAttendees) ? source.OptionalAttendees : []
  ];
  const names = [];
  const emails = [];
  const seenNames = new Set();
  const seenEmails = new Set();
  attendeeCollections.flat().forEach((attendee) => {
    const mailbox = isPlainRecord(attendee?.Mailbox) ? attendee.Mailbox : attendee;
    const name = normalizeOwaText(mailbox?.Name || attendee?.Name || '', 180);
    const email = normalizeOwaText(
      mailbox?.EmailAddress
      || mailbox?.Address
      || attendee?.EmailAddress
      || attendee?.Address
      || '',
      240
    ).toLowerCase();
    if (name && !seenNames.has(name)) {
      seenNames.add(name);
      names.push(name);
    }
    if (email && email.includes('@') && !seenEmails.has(email)) {
      seenEmails.add(email);
      emails.push(email);
    }
  });
  return {
    participantNames: names,
    participantEmails: emails
  };
}

function mapOwaCalendarViewItemToEvent(item = null) {
  const source = isPlainRecord(item) ? item : {};
  const itemId = extractOwaItemId(source.ItemId || source.Id || null);
  const startAt = parseOwaDateTimestamp(source.Start || source.StartDate || source.StartTime || '');
  const endAt = parseOwaDateTimestamp(source.End || source.EndDate || source.EndTime || '');
  const locationText = normalizeOwaText(
    source?.Location?.DisplayName
    || source?.Location?.Name
    || source?.Location
    || '',
    240
  );
  const attendeeInfo = extractOwaAttendees(source);
  const freeBusyType = normalizeOwaFreeBusyType(source.FreeBusyType || source.BusyType || '');
  const eventType = normalizeOwaCalendarEventType(
    /focus|фокус/u.test(String(source.Subject || '')) && source.IsMeeting !== true
      ? 'focus'
      : source.FreeBusyType || source.Subject || ''
  );
  return {
    id: itemId.id || `${source.Subject || 'event'}-${startAt}-${endAt}`,
    owaItemId: itemId.id,
    owaChangeKey: itemId.changeKey,
    title: normalizeOwaText(source.Subject || source.Title || 'Событие', 240) || 'Событие',
    description: '',
    location: locationText,
    joinUrl: extractOwaUrlCandidate(source.JoinOnlineMeetingUrl || locationText || ''),
    startAt,
    endAt,
    type: eventType,
    participantNames: attendeeInfo.participantNames,
    participantEmails: attendeeInfo.participantEmails,
    freeBusyType,
    isMeeting: source.IsMeeting === true,
    isCancelled: source.IsCancelled === true
  };
}

function extractOwaEventBodyHtml(item = null) {
  const bodyValue = item?.Body?.Value || item?.Body?.value || item?.Body || '';
  return typeof bodyValue === 'string' ? bodyValue : '';
}

function extractOwaJoinUrlFromEventItem(item = null) {
  const directUrl = normalizeOwaUrl(item?.JoinOnlineMeetingUrl || '', '');
  if (directUrl) return directUrl;
  const locationCandidates = [
    item?.Location?.DisplayName,
    item?.Location?.Name,
    item?.Location,
    ...(Array.isArray(item?.Locations) ? item.Locations.map((location) => (
      location?.DisplayName || location?.Name || location
    )) : [])
  ];
  for (const candidate of locationCandidates) {
    const resolved = extractOwaUrlCandidate(candidate || '');
    if (resolved) return resolved;
  }
  return extractOwaUrlCandidate(extractOwaEventBodyHtml(item));
}

function mapOwaCalendarEventDetailsToEvent(item = null, fallback = null) {
  const source = isPlainRecord(item) ? item : {};
  const base = isPlainRecord(fallback) ? fallback : {};
  const attendeeInfo = extractOwaAttendees(source);
  const itemId = extractOwaItemId(source.ItemId || source.Id || null);
  const startAt = parseOwaDateTimestamp(source.Start || source.StartDate || source.StartTime || '') || Number(base.startAt || 0);
  const endAt = parseOwaDateTimestamp(source.End || source.EndDate || source.EndTime || '') || Number(base.endAt || 0);
  const locationText = normalizeOwaText(
    source?.Location?.DisplayName
    || source?.Location?.Name
    || source?.Location
    || base.location
    || '',
    240
  );
  return {
    ...base,
    id: itemId.id || normalizeOwaText(base.id || '', 4096),
    owaItemId: itemId.id || normalizeOwaText(base.owaItemId || '', 4096),
    owaChangeKey: itemId.changeKey || normalizeOwaText(base.owaChangeKey || '', 1024),
    title: normalizeOwaText(source.Subject || base.title || 'Событие', 240) || 'Событие',
    description: normalizeOwaText(extractOwaEventBodyHtml(source) || base.description || '', 4000),
    location: locationText,
    joinUrl: extractOwaJoinUrlFromEventItem(source) || normalizeOwaUrl(base.joinUrl || '', ''),
    startAt,
    endAt,
    type: normalizeOwaCalendarEventType(source.FreeBusyType || source.Subject || base.type || ''),
    participantNames: attendeeInfo.participantNames.length
      ? attendeeInfo.participantNames
      : (Array.isArray(base.participantNames) ? base.participantNames : []),
    participantEmails: attendeeInfo.participantEmails.length
      ? attendeeInfo.participantEmails
      : (Array.isArray(base.participantEmails) ? base.participantEmails : []),
    freeBusyType: normalizeOwaFreeBusyType(source.FreeBusyType || base.freeBusyType || ''),
    isMeeting: source.IsMeeting === true || base.isMeeting === true,
    isCancelled: source.IsCancelled === true || base.isCancelled === true
  };
}

async function fetchOwaCalendarEventDetails(event = null, mailUrl = '', eventRecord = null) {
  const mailOrigin = normalizeOwaOrigin(mailUrl);
  const sessionState = ensureOwaReadyState(mailOrigin);
  const baseEvent = isPlainRecord(eventRecord) ? eventRecord : {};
  const itemId = normalizeOwaText(baseEvent.owaItemId || baseEvent.id || '', 4096);
  const changeKey = normalizeOwaText(baseEvent.owaChangeKey || '', 1024);
  if (!itemId) {
    return baseEvent;
  }
  const response = await executeOwaJsonRequest(event, mailUrl, 'GetCalendarEvent', {
    __type: 'GetCalendarEventJsonRequest:#Exchange',
    Header: buildOwaJsonRequestHeaders(sessionState),
    Body: {
      __type: 'GetCalendarEventRequest:#Exchange',
      EventIds: [
        {
          __type: 'ItemId:#Exchange',
          Id: itemId,
          ChangeKey: changeKey
        }
      ],
      ItemShape: {
        __type: 'ItemResponseShape:#Exchange',
        BaseShape: 'IdOnly',
        FilterHtmlContent: true,
        BlockExternalImagesIfSenderUntrusted: true,
        BlockContentFromUnknownSenders: false,
        AddBlankTargetToLinks: true,
        ClientSupportsIrm: true,
        InlineImageUrlTemplate: `service.svc/s/GetFileAttachment?id={id}&X-OWA-CANARY=${encodeURIComponent(sessionState.canary)}`,
        FilterInlineSafetyTips: true,
        MaximumBodySize: 0,
        CssScopeClassName: 'rps_yc',
        BodyType: 'HTML',
        AdditionalProperties: [
          {
            __type: 'ExtendedPropertyUri:#Exchange',
            PropertyTag: '0xe1d',
            PropertyType: 'String'
          },
          {
            __type: 'ExtendedPropertyUri:#Exchange',
            PropertyTag: '0x1016',
            PropertyType: 'Integer'
          }
        ]
      }
    }
  }, {
    actionName: 'GetCalendarEventAction',
    timeoutMs: 18000
  });
  const responseItems = response?.Body?.ResponseMessages?.Items
    || response?.ResponseMessages?.Items
    || [];
  const responseMessage = Array.isArray(responseItems) ? responseItems.find(Boolean) || null : null;
  const item = Array.isArray(responseMessage?.Items) ? responseMessage.Items.find(Boolean) || null : null;
  if (!isPlainRecord(item)) {
    return baseEvent;
  }
  return mapOwaCalendarEventDetailsToEvent(item, baseEvent);
}

async function fetchOwaCalendarEvents(event = null, payload = {}) {
  const mailUrl = normalizeOwaUrl(payload?.mailUrl || '', '');
  const folderState = await ensureOwaCalendarFolderState(event, mailUrl, {
    forceRefresh: payload?.forceFolderRefresh === true
  });
  const rangeStart = Math.max(0, Number(payload?.rangeStart || 0) || (Date.now() - (60 * 60 * 1000)));
  const rangeEnd = Math.max(rangeStart + (15 * 60 * 1000), Number(payload?.rangeEnd || 0) || (Date.now() + (7 * 24 * 60 * 60 * 1000)));
  const response = await executeOwaJsonRequest(event, mailUrl, 'GetCalendarView', {
    __type: 'GetCalendarViewJsonRequest:#Exchange',
    Header: buildOwaJsonRequestHeaders(folderState),
    Body: {
      __type: 'GetCalendarViewRequest:#Exchange',
      CalendarId: {
        __type: 'TargetFolderId:#Exchange',
        BaseFolderId: {
          __type: 'FolderId:#Exchange',
          Id: folderState.calendarFolderId,
          ChangeKey: folderState.calendarFolderChangeKey || 'AgAAAA=='
        }
      },
      RangeStart: formatOwaLocalDateTime(rangeStart, { includeMilliseconds: true }),
      RangeEnd: formatOwaLocalDateTime(rangeEnd, { includeMilliseconds: true })
    }
  }, {
    actionName: 'GetCalendarViewAction_Month',
    timeoutMs: 18000
  }).catch(async (error) => {
    if (folderState.calendarFolderId && payload?.forceFolderRefresh !== true) {
      setStoredOwaSessionState(folderState.origin, {
        ...folderState,
        calendarFolderId: '',
        calendarFolderChangeKey: '',
        calendarFolderName: ''
      });
      return fetchOwaCalendarEvents(event, {
        ...payload,
        forceFolderRefresh: true
      });
    }
    throw error;
  });
  const items = Array.isArray(response?.Body?.Items)
    ? response.Body.Items
    : (Array.isArray(response?.Items) ? response.Items : []);
  const mapped = items
    .map((item) => mapOwaCalendarViewItemToEvent(item))
    .filter((item) => item.id && item.startAt > 0 && item.endAt > item.startAt && item.isCancelled !== true)
    .sort((left, right) => left.startAt - right.startAt);
  const detailCount = Math.max(0, Math.min(8, Number(payload?.detailCount || 6) || 6));
  const includeDetails = payload?.includeDetails !== false;
  let enriched = mapped;
  if (includeDetails && detailCount > 0) {
    const focusIds = new Set(
      mapped
        .filter((entry) => entry.joinUrl || entry.startAt >= (Date.now() - (2 * 60 * 60 * 1000)))
        .slice(0, detailCount)
        .map((entry) => entry.id)
    );
    const nextEvents = [];
    for (const calendarEvent of mapped) {
      if (!focusIds.has(calendarEvent.id)) {
        nextEvents.push(calendarEvent);
        continue;
      }
      try {
        nextEvents.push(await fetchOwaCalendarEventDetails(event, mailUrl, calendarEvent));
      } catch {
        nextEvents.push(calendarEvent);
      }
    }
    enriched = nextEvents;
  }
  return {
    ok: true,
    mailUrl,
    calendarUrl: deriveOwaCalendarUrl(mailUrl),
    folderId: folderState.calendarFolderId,
    folderName: folderState.calendarFolderName,
    events: enriched,
    syncedAt: Date.now()
  };
}

function buildOwaComposeUrl(mailUrl = '', payload = {}) {
  const normalizedMailUrl = normalizeOwaUrl(mailUrl, '');
  if (!normalizedMailUrl) return '';
  const startAt = Math.max(0, Number(payload?.startAt || 0) || 0);
  const endAt = Math.max(startAt, Number(payload?.endAt || 0) || 0);
  return buildOwaUrlWithHash(deriveOwaCalendarUrl(normalizedMailUrl) || normalizedMailUrl, '/calendar/action/compose', {
    subject: normalizeOwaText(payload?.subject || '', 240),
    body: normalizeOwaText(payload?.body || '', 8000),
    location: normalizeOwaText(payload?.location || '', 240),
    startdt: startAt > 0 ? formatOwaOffsetDateTime(startAt) : '',
    enddt: endAt > startAt ? formatOwaOffsetDateTime(endAt) : '',
    allday: payload?.allDay === true ? 'true' : 'false'
  });
}

function isAllowedOwaWindowUrl(targetUrl = '', allowedOrigin = '') {
  const normalizedUrl = normalizeOwaUrl(targetUrl, '');
  if (!normalizedUrl) return false;
  try {
    const parsed = new URL(normalizedUrl);
    if (parsed.protocol === 'about:') return true;
    return normalizeOwaOrigin(allowedOrigin) === parsed.origin;
  } catch {
    return false;
  }
}

function installOwaNavigationHandlers(webContents, allowedOrigin = '') {
  webContents.setWindowOpenHandler(({ url = '' }) => {
    const normalizedUrl = normalizeOwaUrl(url, '');
    if (isAllowedOwaWindowUrl(normalizedUrl, allowedOrigin)) {
      return {
        action: 'allow',
        overrideBrowserWindowOptions: {
          width: 1240,
          height: 900,
          minWidth: 900,
          minHeight: 680,
          backgroundColor: '#eef2f8',
          webPreferences: {
            sandbox: true,
            contextIsolation: true,
            partition: YUCHAT_SESSION_PARTITION
          }
        }
      };
    }
    if (isSafeExternalUrl(normalizedUrl)) {
      void shell.openExternal(normalizedUrl);
    }
    return { action: 'deny' };
  });

  webContents.on('will-navigate', (event, url) => {
    if (isAllowedOwaWindowUrl(url, allowedOrigin)) {
      return;
    }
    event.preventDefault();
    if (isSafeExternalUrl(url)) {
      void shell.openExternal(url);
    }
  });
}

async function openOwaWindow(event = null, payload = {}) {
  const mailUrl = normalizeOwaUrl(payload?.mailUrl || payload?.url || '', '');
  const origin = normalizeOwaOrigin(mailUrl);
  if (!mailUrl || !origin) {
    throw Object.assign(new Error('Некорректный адрес OWA.'), {
      code: 'OWA_URL_INVALID'
    });
  }
  const calendarUrl = normalizeOwaUrl(
    payload?.calendarUrl || '',
    deriveOwaCalendarUrl(mailUrl) || mailUrl
  );
  const requestedView = normalizeOwaText(payload?.view || 'calendar', 24).toLowerCase();
  const targetUrl = normalizeOwaUrl(
    payload?.targetUrl || (
      requestedView === 'mail'
        ? buildOwaUrlWithHash(mailUrl, '/mail')
        : requestedView === 'compose'
          ? buildOwaComposeUrl(calendarUrl || mailUrl, payload?.compose || {})
          : buildOwaUrlWithHash(calendarUrl || deriveOwaCalendarUrl(mailUrl) || mailUrl, '/calendar')
    ),
    ''
  );
  if (!targetUrl) {
    throw Object.assign(new Error('Не удалось подготовить ссылку OWA.'), {
      code: 'OWA_URL_INVALID'
    });
  }
  let owaWindow = owaWindowsByOrigin.get(origin) || null;
  const backgroundConnectRequested = payload?.background === true;
  if (!(owaWindow instanceof BrowserWindow) || owaWindow.isDestroyed()) {
    owaWindow = new BrowserWindow({
      width: 1240,
      height: 900,
      minWidth: 900,
      minHeight: 680,
      show: false,
      backgroundColor: '#eef2f8',
      title: 'Почта и календарь',
      webPreferences: {
        sandbox: true,
        contextIsolation: true,
        partition: YUCHAT_SESSION_PARTITION
      }
    });
    owaWindowsByOrigin.set(origin, owaWindow);
    owaWindow.__yuOwaOrigin = origin;
    owaWindow.__yuOwaBackgroundConnect = backgroundConnectRequested;
    owaWindow.__yuOwaAutoRevealTimer = 0;
    owaWindow.webContents.setUserAgent(CUSTOM_YUCHAT_USER_AGENT);
    configureYuchatSession(owaWindow.webContents.session);
    attachOwaRequestCapture(owaWindow.webContents.session);
    installOwaNavigationHandlers(owaWindow.webContents, origin);
    owaWindow.once('ready-to-show', () => {
      if (!owaWindow || owaWindow.isDestroyed()) return;
      if (owaWindow.__yuOwaBackgroundConnect === true) {
        return;
      }
      owaWindow.show();
    });
    owaWindow.webContents.on('did-navigate', (_event, url) => {
      maybeRevealOwaWindowForInteractiveAuth(owaWindow, origin, url);
    });
    owaWindow.webContents.on('did-redirect-navigation', (_event, url) => {
      maybeRevealOwaWindowForInteractiveAuth(owaWindow, origin, url);
    });
    owaWindow.on('close', () => {
      clearOwaAutoRevealTimer(owaWindow);
      scheduleYuchatSessionFlush(0);
    });
    owaWindow.on('closed', () => {
      clearOwaAutoRevealTimer(owaWindow);
      owaWindowsByOrigin.delete(origin);
    });
    await restorePersistedYuchatSessionCookies(owaWindow.webContents.session).catch(() => {});
  }
  const shouldKeepHidden = backgroundConnectRequested && !owaWindow.isVisible();
  owaWindow.__yuOwaBackgroundConnect = shouldKeepHidden;
  setStoredOwaSessionState(origin, {
    ...getStoredOwaSessionState(origin),
    lastKnownMailUrl: mailUrl,
    lastKnownCalendarUrl: calendarUrl
  });
  if (shouldKeepHidden) {
    scheduleOwaAutoReveal(owaWindow, origin);
  } else {
    clearOwaAutoRevealTimer(owaWindow);
  }
  if (owaWindow.webContents.getURL() !== targetUrl) {
    await owaWindow.loadURL(targetUrl);
  } else if (!shouldKeepHidden && !owaWindow.isVisible()) {
    revealOwaWindow(owaWindow);
  }
  if (shouldKeepHidden) {
    scheduleOwaAutoReveal(owaWindow, origin);
  } else {
    revealOwaWindow(owaWindow);
  }
  return {
    ok: true,
    origin,
    targetUrl,
    background: shouldKeepHidden
  };
}

function buildOwaAvailabilityRequest(sessionState = {}, attendeeEmails = [], options = {}) {
  const uniqueEmails = Array.from(new Set(
    (Array.isArray(attendeeEmails) ? attendeeEmails : [])
      .map((email) => normalizeOwaText(email || '', 240).toLowerCase())
      .filter((email) => email && email.includes('@'))
  ));
  return {
    __type: 'GetUserAvailabilityJsonRequest:#Exchange',
    Header: buildOwaJsonRequestHeaders(sessionState),
    Body: {
      __type: 'GetUserAvailabilityRequest:#Exchange',
      MailboxDataArray: uniqueEmails.map((email) => ({
        __type: 'MailboxData:#Exchange',
        Email: {
          __type: 'EmailAddress:#Exchange',
          Address: email
        },
        AttendeeType: 'Required',
        ExcludeConflicts: false
      })),
      FreeBusyViewOptions: {
        __type: 'FreeBusyViewOptions:#Exchange',
        TimeWindow: {
          __type: 'Duration:#Exchange',
          StartTime: formatOwaLocalDateTime(options.rangeStart || Date.now()),
          EndTime: formatOwaLocalDateTime(options.rangeEnd || (Date.now() + (7 * 24 * 60 * 60 * 1000)))
        },
        MergedFreeBusyIntervalInMinutes: Math.max(5, Math.min(120, Number(options.intervalMinutes || 30) || 30)),
        RequestedView: normalizeOwaText(options.requestedView || 'Detailed', 32) || 'Detailed'
      }
    }
  };
}

function extractOwaAvailabilityViews(response = null) {
  const directResponses = response?.Body?.Responses
    || response?.Responses
    || response?.Body?.FreeBusyResponseArray
    || response?.FreeBusyResponseArray
    || [];
  if (Array.isArray(directResponses) && directResponses.length) {
    return directResponses.map((entry) => (
      (isPlainRecord(entry?.FreeBusyView) && entry.FreeBusyView)
      || (isPlainRecord(entry?.CalendarView) && entry.CalendarView)
      || entry
    ));
  }
  const collected = [];
  const visit = (node) => {
    if (Array.isArray(node)) {
      node.forEach((item) => visit(item));
      return;
    }
    if (!isPlainRecord(node)) return;
    if (isPlainRecord(node.FreeBusyView)) {
      collected.push(node.FreeBusyView);
    } else if (Array.isArray(node.CalendarEventArray) || typeof node.MergedFreeBusy === 'string') {
      collected.push(node);
    }
    Object.values(node).forEach((value) => visit(value));
  };
  visit(response);
  return collected;
}

function mapOwaBusyIntervalsFromView(view = null, options = {}) {
  const source = isPlainRecord(view) ? view : {};
  const calendarEvents = Array.isArray(source.CalendarEventArray)
    ? source.CalendarEventArray
    : (Array.isArray(source.Items) ? source.Items : []);
  if (!calendarEvents.length && typeof source.MergedFreeBusy === 'string') {
    const intervalMinutes = Math.max(5, Math.min(120, Number(options?.intervalMinutes || 30) || 30));
    const rangeStart = Math.max(0, Number(options?.rangeStart || 0) || 0);
    if (!rangeStart) {
      return [];
    }
    const intervalMs = intervalMinutes * 60 * 1000;
    const normalizedMergedView = String(source.MergedFreeBusy || '').trim();
    const busyIntervals = [];
    let currentStartAt = 0;
    let currentFreeBusyType = '';
    for (let index = 0; index <= normalizedMergedView.length; index += 1) {
      const token = index < normalizedMergedView.length
        ? String(normalizedMergedView[index] || '').trim()
        : '';
      const isBusy = Boolean(token && token !== '0');
      if (isBusy && !currentStartAt) {
        currentStartAt = rangeStart + (index * intervalMs);
        currentFreeBusyType = token;
        continue;
      }
      if (isBusy) {
        continue;
      }
      if (!currentStartAt) {
        continue;
      }
      const endAt = rangeStart + (index * intervalMs);
      if (endAt > currentStartAt) {
        busyIntervals.push({
          startAt: currentStartAt,
          endAt,
          freeBusyType: currentFreeBusyType || 'merged'
        });
      }
      currentStartAt = 0;
      currentFreeBusyType = '';
    }
    return busyIntervals;
  }
  return calendarEvents
    .map((item) => {
      const startAt = parseOwaDateTimestamp(item?.StartTime || item?.Start || item?.StartDate || '');
      const endAt = parseOwaDateTimestamp(item?.EndTime || item?.End || item?.EndDate || '');
      const freeBusyType = normalizeOwaFreeBusyType(item?.BusyType || item?.FreeBusyType || '');
      if (!startAt || !endAt || endAt <= startAt || !shouldTreatOwaBusyTypeAsBusy(freeBusyType)) {
        return null;
      }
      return {
        startAt,
        endAt,
        freeBusyType
      };
    })
    .filter(Boolean)
    .sort((left, right) => left.startAt - right.startAt);
}

function computeCommonAvailabilitySlots(attendees = [], options = {}) {
  const durationMinutes = Math.max(15, Math.min(240, Number(options.durationMinutes || 30) || 30));
  const intervalMinutes = Math.max(15, Math.min(120, Number(options.intervalMinutes || 30) || 30));
  const durationMs = durationMinutes * 60 * 1000;
  const intervalMs = intervalMinutes * 60 * 1000;
  const rangeStart = Math.max(Date.now(), Number(options.rangeStart || 0) || Date.now());
  const rangeEnd = Math.max(rangeStart + durationMs, Number(options.rangeEnd || 0) || (rangeStart + (7 * 24 * 60 * 60 * 1000)));
  const maxSuggestions = Math.max(1, Math.min(12, Number(options.maxSuggestions || 6) || 6));
  const normalizeMinuteOfDay = (value, fallback) => {
    const numericValue = Math.round(Number(value));
    if (!Number.isFinite(numericValue)) return fallback;
    return Math.max(0, Math.min(24 * 60, numericValue));
  };
  const legacyWorkDayStartMinutes = (
    (Math.max(0, Math.min(23, Number(options.workDayStartHour || 9) || 9)) * 60)
    + Math.max(0, Math.min(59, Number(options.workDayStartMinute || 0) || 0))
  );
  const legacyWorkDayEndMinutes = (
    (Math.max(0, Math.min(24, Number(options.workDayEndHour || 18) || 18)) * 60)
    + Math.max(0, Math.min(59, Number(options.workDayEndMinute || 0) || 0))
  );
  const workDayStartMinutes = normalizeMinuteOfDay(
    options.workDayStartMinutes,
    legacyWorkDayStartMinutes
  );
  const requestedWorkDayEndMinutes = normalizeMinuteOfDay(
    options.workDayEndMinutes,
    legacyWorkDayEndMinutes
  );
  const workDayEndMinutes = Math.max(
    Math.min(24 * 60, workDayStartMinutes + durationMinutes),
    requestedWorkDayEndMinutes
  );
  const normalizedAttendees = (Array.isArray(attendees) ? attendees : [])
    .map((attendee) => ({
      email: normalizeOwaText(attendee?.email || '', 240).toLowerCase(),
      busy: Array.isArray(attendee?.busy) ? attendee.busy : []
    }))
    .filter((attendee) => attendee.email);
  if (!normalizedAttendees.length) return [];
  const suggestions = [];
  for (let cursor = new Date(rangeStart); cursor.getTime() < rangeEnd && suggestions.length < maxSuggestions; cursor.setDate(cursor.getDate() + 1)) {
    const dayStart = new Date(cursor);
    dayStart.setHours(Math.floor(workDayStartMinutes / 60), workDayStartMinutes % 60, 0, 0);
    const dayEnd = new Date(cursor);
    dayEnd.setHours(Math.floor(workDayEndMinutes / 60), workDayEndMinutes % 60, 0, 0);
    let slotStart = Math.max(rangeStart, dayStart.getTime());
    const slotWindowEnd = Math.min(rangeEnd, dayEnd.getTime());
    while ((slotStart + durationMs) <= slotWindowEnd && suggestions.length < maxSuggestions) {
      const slotEnd = slotStart + durationMs;
      const hasBusyOverlap = normalizedAttendees.some((attendee) => attendee.busy.some((interval) => (
        Number(interval?.startAt || 0) < slotEnd && Number(interval?.endAt || 0) > slotStart
      )));
      if (!hasBusyOverlap) {
        suggestions.push({
          startAt: slotStart,
          endAt: slotEnd,
          durationMinutes
        });
      }
      slotStart += intervalMs;
    }
  }
  return suggestions;
}

async function findOwaMeetingSlots(event = null, payload = {}) {
  const mailUrl = normalizeOwaUrl(payload?.mailUrl || '', '');
  const origin = normalizeOwaOrigin(mailUrl);
  const sessionState = await ensureOwaCalendarFolderState(event, mailUrl);
  const attendeeEmails = Array.from(new Set(
    (Array.isArray(payload?.attendeeEmails) ? payload.attendeeEmails : [])
      .map((email) => normalizeOwaText(email || '', 240).toLowerCase())
      .filter((email) => email && email.includes('@'))
  ));
  if (!attendeeEmails.length) {
    const error = new Error('Не переданы email участников для поиска слота.');
    error.code = 'OWA_ATTENDEES_MISSING';
    throw error;
  }
  const rangeStart = Math.max(Date.now(), Number(payload?.rangeStart || 0) || Date.now());
  const rangeEnd = Math.max(rangeStart + (30 * 60 * 1000), Number(payload?.rangeEnd || 0) || (rangeStart + (7 * 24 * 60 * 60 * 1000)));
  const intervalMinutes = payload?.intervalMinutes || 30;
  const runAvailabilityRequest = async (requestedView = 'Detailed') => {
    const requestPayload = buildOwaAvailabilityRequest(sessionState, attendeeEmails, {
      rangeStart,
      rangeEnd,
      intervalMinutes,
      requestedView
    });
    const response = await executeOwaJsonRequest(event, mailUrl, 'GetUserAvailability', requestPayload, {
      actionName: 'GetUserAvailabilityAction',
      timeoutMs: 18000
    });
    return extractOwaAvailabilityViews(response);
  };
  let views = [];
  try {
    views = await runAvailabilityRequest('FreeBusyMerged');
  } catch {
    views = [];
  }
  const hasUsableFastViews = Array.isArray(views)
    && views.length >= attendeeEmails.length
    && views.every((view) => (
      isPlainRecord(view)
      && (
        Array.isArray(view.CalendarEventArray)
        || Array.isArray(view.Items)
        || typeof view.MergedFreeBusy === 'string'
      )
    ));
  if (!hasUsableFastViews) {
    views = await runAvailabilityRequest('Detailed');
  }
  const attendees = attendeeEmails.map((email, index) => ({
    email,
    busy: mapOwaBusyIntervalsFromView(views[index] || null, {
      rangeStart,
      intervalMinutes
    })
  }));
  return {
    ok: true,
    origin,
    attendees,
    slots: computeCommonAvailabilitySlots(attendees, {
      durationMinutes: payload?.durationMinutes || 30,
      intervalMinutes: payload?.intervalMinutes || 30,
      rangeStart,
      rangeEnd,
      maxSuggestions: payload?.maxSuggestions || 6,
      workDayStartHour: payload?.workDayStartHour || 9,
      workDayStartMinute: payload?.workDayStartMinute || 0,
      workDayEndHour: payload?.workDayEndHour || 18,
      workDayEndMinute: payload?.workDayEndMinute || 30,
      workDayStartMinutes: payload?.workDayStartMinutes,
      workDayEndMinutes: payload?.workDayEndMinutes
    })
  };
}

function buildOwaErrorPayload(error = null, fallbackCode = 'OWA_ERROR') {
  const code = normalizeOwaText(error?.code || fallbackCode, 64) || fallbackCode;
  const message = normalizeOwaText(error?.message || 'Не удалось выполнить запрос OWA.', 240)
    || 'Не удалось выполнить запрос OWA.';
  return {
    ok: false,
    code,
    error: message,
    status: Math.max(0, Number(error?.status || 0) || 0)
  };
}

function registerTransferAbortHandler(transferId = '', handler = null) {
  const normalizedTransferId = trimText(transferId || '', 180);
  if (!normalizedTransferId || typeof handler !== 'function') return '';
  activeTransferAbortHandlersById.set(normalizedTransferId, handler);
  return normalizedTransferId;
}

function unregisterTransferAbortHandler(transferId = '') {
  const normalizedTransferId = trimText(transferId || '', 180);
  if (!normalizedTransferId) return;
  activeTransferAbortHandlersById.delete(normalizedTransferId);
}

function abortTransferOperation(transferId = '', reason = 'canceled') {
  const normalizedTransferId = trimText(transferId || '', 180);
  if (!normalizedTransferId) {
    return { ok: false, active: false };
  }
  const handler = activeTransferAbortHandlersById.get(normalizedTransferId);
  if (typeof handler !== 'function') {
    return { ok: false, active: false };
  }
  try {
    handler(normalizeTransferAbortReason(reason));
    return { ok: true, active: true };
  } catch (error) {
    return {
      ok: false,
      active: true,
      error: trimText(error?.message || 'Не удалось остановить операцию', 220)
    };
  }
}

function normalizeDiagnosticsTimestampMs(value = 0) {
  const raw = Number(value || 0);
  if (!Number.isFinite(raw) || raw <= 0) {
    return Date.now();
  }

  let normalized = raw;
  if (normalized > 9e13) {
    normalized = Math.round(normalized / 1000);
  } else if (normalized > 9e11) {
    normalized = Math.round(normalized);
  } else if (normalized > 9e8) {
    normalized = Math.round(normalized * 1000);
  } else {
    normalized = Date.now();
  }

  const earliestMs = Date.UTC(2010, 0, 1);
  const latestMs = Date.UTC(2100, 0, 1);
  if (normalized < earliestMs || normalized > latestMs) {
    return Date.now();
  }
  return normalized;
}

function normalizeHeaderPairs(headerMap = null) {
  if (!headerMap || typeof headerMap !== 'object') return [];
  const pairs = [];
  Object.entries(headerMap).forEach(([rawName, rawValue]) => {
    const name = String(rawName || '').trim();
    if (!name) return;
    if (Array.isArray(rawValue)) {
      rawValue.forEach((value) => {
        pairs.push({
          name,
          value: trimText(value == null ? '' : String(value), 5000)
        });
      });
      return;
    }
    pairs.push({
      name,
      value: trimText(rawValue == null ? '' : String(rawValue), 5000)
    });
  });
  return pairs;
}

function getHeaderValue(headerPairs = [], targetName = '') {
  const normalizedTarget = String(targetName || '').trim().toLowerCase();
  if (!normalizedTarget) return '';
  const pair = (Array.isArray(headerPairs) ? headerPairs : [])
    .find((item) => String(item?.name || '').trim().toLowerCase() === normalizedTarget);
  return pair ? String(pair.value || '') : '';
}

function buildHarQueryString(urlValue = '') {
  try {
    const parsed = new URL(String(urlValue || '').trim());
    const query = [];
    parsed.searchParams.forEach((value, name) => {
      query.push({ name, value: trimText(value, 3000) });
    });
    return query;
  } catch {
    return [];
  }
}

function estimateUploadDataSizeBytes(details = {}) {
  const uploadData = Array.isArray(details?.uploadData) ? details.uploadData : [];
  let totalSize = 0;
  uploadData.forEach((part) => {
    if (part?.bytes) {
      try {
        if (Buffer.isBuffer(part.bytes)) {
          totalSize += part.bytes.length;
        } else if (part.bytes instanceof ArrayBuffer) {
          totalSize += part.bytes.byteLength;
        } else {
          totalSize += Buffer.byteLength(String(part.bytes || ''));
        }
      } catch {}
    }
    if (part?.file) {
      try {
        const stat = fs.statSync(String(part.file || ''));
        if (stat?.isFile?.()) {
          totalSize += Number(stat.size || 0);
        }
      } catch {}
    }
  });
  return Math.max(0, Number(totalSize) || 0);
}

function getOrCreateDiagnosticsRequestEntry(details = {}) {
  if (!diagnosticsState) return null;
  const requestId = String(details?.id ?? details?.requestId ?? '').trim();
  if (!requestId) return null;
  const existing = diagnosticPendingRequestsById.get(requestId);
  if (existing) return existing;

  const startedAtMs = normalizeDiagnosticsTimestampMs(details?.timestamp);
  const next = {
    requestId,
    url: trimText(details?.url || '', 8192),
    method: trimText((details?.method || 'GET').toUpperCase(), 24) || 'GET',
    resourceType: trimText(details?.resourceType || 'other', 40) || 'other',
    startedAtMs,
    startedDateTime: new Date(startedAtMs).toISOString(),
    requestHeaders: [],
    responseHeaders: [],
    requestBodySize: 0,
    responseBodySize: 0,
    status: 0,
    statusText: '',
    error: '',
    fromCache: false,
    ip: '',
    protocol: '',
    webContentsId: Number(details?.webContentsId || 0) || 0
  };
  diagnosticPendingRequestsById.set(requestId, next);
  return next;
}

function appendDiagnosticsNetworkEntry(entry = null) {
  if (!diagnosticsState || !entry || typeof entry !== 'object') return;
  diagnosticNetworkEntries.push(entry);
  clampCollectionSize(diagnosticNetworkEntries, DIAGNOSTICS_MAX_NETWORK_ENTRIES);
}

function finalizeDiagnosticsRequest(details = {}, patch = {}) {
  if (!diagnosticsState) return;
  const requestId = String(details?.id ?? details?.requestId ?? '').trim();
  if (!requestId) return;
  const entry = getOrCreateDiagnosticsRequestEntry(details);
  if (!entry) return;
  const finishedAtMs = normalizeDiagnosticsTimestampMs(details?.timestamp || Date.now());

  entry.url = trimText(details?.url || entry.url, 8192);
  entry.method = trimText((details?.method || entry.method || 'GET').toUpperCase(), 24) || 'GET';
  entry.resourceType = trimText(details?.resourceType || entry.resourceType || 'other', 40) || 'other';
  entry.status = Number(patch?.status ?? details?.statusCode ?? entry.status) || 0;
  entry.statusText = trimText(patch?.statusText || details?.statusLine || entry.statusText, 600);
  entry.error = trimText(patch?.error || details?.error || entry.error, 1200);
  entry.fromCache = Boolean(details?.fromCache === true || entry.fromCache);
  entry.ip = trimText(details?.ip || entry.ip, 180);
  entry.protocol = trimText(details?.protocol || entry.protocol, 120);
  if (patch?.responseHeaders) {
    entry.responseHeaders = patch.responseHeaders;
  }
  if (patch?.requestHeaders) {
    entry.requestHeaders = patch.requestHeaders;
  }
  if (Number.isFinite(Number(patch?.requestBodySize))) {
    entry.requestBodySize = Math.max(entry.requestBodySize, Number(patch.requestBodySize || 0));
  }
  if (Number.isFinite(Number(patch?.responseBodySize))) {
    entry.responseBodySize = Math.max(entry.responseBodySize, Number(patch.responseBodySize || 0));
  } else {
    entry.responseBodySize = Math.max(entry.responseBodySize, Number(details?.encodedDataLength || 0) || 0);
  }
  entry.completedAtMs = Math.max(entry.startedAtMs, finishedAtMs);
  entry.completedDateTime = new Date(entry.completedAtMs).toISOString();
  entry.durationMs = Math.max(0, entry.completedAtMs - entry.startedAtMs);
  entry.pending = patch?.pending === true;
  appendDiagnosticsNetworkEntry({ ...entry });
  diagnosticPendingRequestsById.delete(requestId);
}

function appendDiagnosticsConsoleEntry(payload = {}) {
  if (!diagnosticsState) return;
  const levelMap = ['verbose', 'info', 'warning', 'error'];
  const rawLevel = Number(payload?.level);
  const level = Number.isFinite(rawLevel) && rawLevel >= 0 && rawLevel < levelMap.length
    ? levelMap[rawLevel]
    : trimText(payload?.level || 'info', 40) || 'info';
  diagnosticConsoleEntries.push({
    at: new Date().toISOString(),
    level,
    message: trimText(payload?.message || '', 16000),
    line: Number(payload?.line || 0) || 0,
    sourceId: trimText(payload?.sourceId || '', 1024),
    webContentsId: Number(payload?.webContentsId || 0) || 0,
    event: trimText(payload?.event || '', 120)
  });
  clampCollectionSize(diagnosticConsoleEntries, DIAGNOSTICS_MAX_CONSOLE_ENTRIES);
}

function buildDiagnosticsHarEntry(networkEntry = {}) {
  const startedDateTime = String(networkEntry?.startedDateTime || new Date().toISOString());
  const time = Math.max(0, Number(networkEntry?.durationMs || 0));
  const requestHeaders = Array.isArray(networkEntry?.requestHeaders) ? networkEntry.requestHeaders : [];
  const responseHeaders = Array.isArray(networkEntry?.responseHeaders) ? networkEntry.responseHeaders : [];
  const mimeType = getHeaderValue(responseHeaders, 'content-type') || 'application/octet-stream';
  const redirectURL = getHeaderValue(responseHeaders, 'location') || '';
  const entry = {
    startedDateTime,
    time,
    request: {
      method: String(networkEntry?.method || 'GET'),
      url: String(networkEntry?.url || ''),
      httpVersion: String(networkEntry?.protocol || ''),
      headers: requestHeaders,
      queryString: buildHarQueryString(networkEntry?.url || ''),
      cookies: [],
      headersSize: -1,
      bodySize: Math.max(0, Number(networkEntry?.requestBodySize || 0))
    },
    response: {
      status: Number(networkEntry?.status || 0),
      statusText: String(networkEntry?.statusText || ''),
      httpVersion: String(networkEntry?.protocol || ''),
      headers: responseHeaders,
      cookies: [],
      content: {
        size: Math.max(0, Number(networkEntry?.responseBodySize || 0)),
        mimeType
      },
      redirectURL,
      headersSize: -1,
      bodySize: Math.max(0, Number(networkEntry?.responseBodySize || 0))
    },
    cache: {},
    timings: {
      send: 0,
      wait: time,
      receive: 0
    },
    pageref: 'page_1'
  };

  if (networkEntry?.ip) {
    entry.serverIPAddress = String(networkEntry.ip);
  }
  if (networkEntry?.error) {
    entry._comment = `Request failed: ${String(networkEntry.error)}`;
  } else if (networkEntry?.pending) {
    entry._comment = 'Request was still pending at export time.';
  }
  return entry;
}

function flushDiagnosticsArtifacts(options = {}) {
  if (!diagnosticsState) return;
  if (diagnosticFlushTimer) {
    clearTimeout(diagnosticFlushTimer);
    diagnosticFlushTimer = 0;
  }

  const includePending = options?.includePending !== false;
  const networkEntries = diagnosticNetworkEntries.map((entry) => ({ ...entry }));
  if (includePending) {
    Array.from(diagnosticPendingRequestsById.values()).forEach((pendingEntry) => {
      const finishedAtMs = Date.now();
      networkEntries.push({
        ...pendingEntry,
        pending: true,
        completedAtMs: finishedAtMs,
        completedDateTime: new Date(finishedAtMs).toISOString(),
        durationMs: Math.max(0, finishedAtMs - Number(pendingEntry?.startedAtMs || finishedAtMs))
      });
    });
  }
  const sortedNetworkEntries = networkEntries.sort((left, right) => (
    Number(left?.startedAtMs || 0) - Number(right?.startedAtMs || 0)
  ));

  const harPayload = {
    log: {
      version: '1.2',
      creator: {
        name: 'Yuchat_custom diagnostics',
        version: app.getVersion()
      },
      pages: [
        {
          startedDateTime: diagnosticsState.startedAt,
          id: 'page_1',
          title: mainWindow && !mainWindow.isDestroyed()
            ? trimText(mainWindow.webContents.getTitle?.() || '', 300)
            : '',
          pageTimings: {}
        }
      ],
      entries: sortedNetworkEntries.map((entry) => buildDiagnosticsHarEntry(entry))
    }
  };

  const summaryPayload = {
    startedAt: diagnosticsState.startedAt,
    updatedAt: new Date().toISOString(),
    consoleEntryCount: diagnosticConsoleEntries.length,
    networkEntryCount: sortedNetworkEntries.length,
    pendingRequestCount: diagnosticPendingRequestsById.size,
    currentUrl: mainWindow && !mainWindow.isDestroyed()
      ? trimText(mainWindow.webContents.getURL() || '', 2400)
      : '',
    artifacts: {
      summaryPath: diagnosticsSummaryPath,
      consolePath: diagnosticsConsolePath,
      harPath: diagnosticsHarPath,
      rawNetworkPath: diagnosticsRawNetworkPath
    }
  };

  try {
    ensureDirSync(diagnosticsArtifactsDir);
    const consoleJsonl = diagnosticConsoleEntries.map((entry) => JSON.stringify(entry)).join('\n');
    fs.writeFileSync(diagnosticsConsolePath, consoleJsonl ? `${consoleJsonl}\n` : '', 'utf8');
    fs.writeFileSync(diagnosticsRawNetworkPath, JSON.stringify(sortedNetworkEntries, null, 2), 'utf8');
    fs.writeFileSync(diagnosticsHarPath, JSON.stringify(harPayload, null, 2), 'utf8');
    fs.writeFileSync(diagnosticsSummaryPath, JSON.stringify(summaryPayload, null, 2), 'utf8');
    diagnosticsState.flushCount += 1;
  } catch (error) {
    runtimeWarn('[YuChat] Failed to flush diagnostics artifacts:', error);
  }
}

function scheduleDiagnosticsFlush(delay = 900) {
  if (!diagnosticsState) return;
  if (diagnosticFlushTimer) {
    clearTimeout(diagnosticFlushTimer);
  }
  diagnosticFlushTimer = setTimeout(() => {
    diagnosticFlushTimer = 0;
    flushDiagnosticsArtifacts({ includePending: true });
  }, Math.max(120, Number(delay) || 900));
}

function toSerializableError(error) {
  if (!error) {
    return { message: 'Unknown error' };
  }

  if (typeof error === 'string') {
    return { message: error };
  }

  return {
    name: typeof error.name === 'string' ? error.name : 'Error',
    message: typeof error.message === 'string' ? error.message : String(error),
    stack: typeof error.stack === 'string' ? error.stack : ''
  };
}

function recordSmokeEvent(name, details = {}) {
  if (!smokeTestState) return;

  smokeTestState.events.push({
    at: new Date().toISOString(),
    name,
    ...details
  });
  appendSmokeLog(`event:${name} ${JSON.stringify(details)}`);
}

function addSmokeFailure(reason, details = {}) {
  if (!smokeTestState) return;

  smokeTestState.failures.push({
    at: new Date().toISOString(),
    reason,
    ...details
  });
  appendSmokeLog(`failure:${reason}`);
}

function isTrustedSmokeUrl(targetUrl = '') {
  try {
    const parsed = new URL(targetUrl);
    return parsed.protocol === 'https:' && (
      parsed.hostname === 'yuchat.rt.ru' ||
      parsed.hostname.endsWith('.rt.ru')
    );
  } catch {
    return false;
  }
}

function isLikelyChromiumErrorText(text = '') {
  const normalizedText = normalizeText(text);
  if (!normalizedText) return false;

  const patterns = [
    'this site can’t be reached',
    'this site can\'t be reached',
    'err_',
    'check if there is a typo',
    'не удается получить доступ к сайту',
    'страница недоступна',
    'веб-страница недоступна'
  ];

  return patterns.some((pattern) => normalizedText.includes(normalizeText(pattern)));
}

async function collectShellSnapshot() {
  if (!mainWindow || mainWindow.isDestroyed()) {
    return null;
  }

  try {
    return await mainWindow.webContents.executeJavaScript(`(() => ({
      documentTitle: document.title || '',
      hasPanel: Boolean(document.querySelector('.panel')),
      titleText: document.querySelector('.title')?.textContent?.trim() || document.title || '',
      subtitleText: document.querySelector('.subtitle')?.textContent?.trim() || '',
      statusTitle: document.querySelector('.status-title')?.textContent?.trim() || '',
      statusText: document.querySelector('.status-text')?.textContent?.trim() || ''
    }))()`, true);
  } catch (error) {
    return {
      error: toSerializableError(error)
    };
  }
}

async function collectViewSnapshot() {
  const yuchatContents = mainWindow && !mainWindow.isDestroyed()
    ? mainWindow.webContents
    : null;
  if (!yuchatContents || yuchatContents.isDestroyed()) {
    return null;
  }

  try {
    return await yuchatContents.executeJavaScript(`(() => {
      const bodyText = document.body?.innerText?.replace(/\\s+/g, ' ').trim() || '';
      const bodyChildren = Array.from(document.body?.children || []).slice(0, 12).map((node) => ({
        tag: String(node?.tagName || '').toLowerCase(),
        id: String(node?.id || ''),
        className: String(node?.className || '').trim().slice(0, 160)
      }));

      return {
        documentTitle: document.title || '',
        readyState: document.readyState || '',
        hasBody: Boolean(document.body),
        bodyPreview: bodyText.slice(0, 600),
        hasPrebootStyle: Boolean(document.getElementById('yuchat-preboot-style')),
        hasCustomStyle: Boolean(document.getElementById('yuchat-full-custom-style')),
        hasCustomRoot: Boolean(document.getElementById('yuchat-full-custom-root')),
        nativeProfileOpen: document.body?.classList.contains('yc-native-profile-open') === true,
        bootstrapMarker: document.documentElement?.getAttribute('data-yu-bootstrap-preload') || '',
        fullPreloadMarker: document.documentElement?.getAttribute('data-yu-full-preload') || '',
        shellMarker: document.documentElement?.getAttribute('data-yu-shell-active') || '',
        layoutMarker: document.documentElement?.getAttribute('data-yu-layout-ready') || '',
        bodyChildren
      };
    })()`, true);
  } catch (error) {
    return {
      error: toSerializableError(error)
    };
  }
}

async function captureSmokeScreenshot() {
  if (!smokeTestState) return '';

  ensureDirSync(smokeArtifactsDir);

  try {
    let image = null;

    if (mainWindow && !mainWindow.isDestroyed()) {
      image = await mainWindow.capturePage();
    }

    if (!image || image.isEmpty()) {
      return '';
    }

    fs.writeFileSync(smokeScreenshotPath, image.toPNG());
    smokeTestState.artifacts.screenshotPath = smokeScreenshotPath;
    return smokeScreenshotPath;
  } catch (error) {
    addSmokeFailure('Failed to capture smoke screenshot.', {
      error: toSerializableError(error)
    });
    return '';
  }
}

function scheduleSmokeEvaluation(trigger, delay = 1200) {
  if (!smokeTestState || smokeFinalizeInFlight) return;

  if (smokeEvaluationTimer) {
    clearTimeout(smokeEvaluationTimer);
  }

  smokeEvaluationTimer = setTimeout(() => {
    smokeEvaluationTimer = 0;
    void evaluateSmokeTest(trigger);
  }, Math.max(0, Number(delay) || 0));
}

async function finalizeSmokeTest(ok, reason) {
  if (!smokeTestState) return;

  if (smokeFinalizeInFlight) {
    return smokeFinalizeInFlight;
  }

  smokeFinalizeInFlight = (async () => {
    appendSmokeLog(`finalize:start ok=${Boolean(ok)} reason=${reason || ''}`);
    if (smokeTimeoutHandle) {
      clearTimeout(smokeTimeoutHandle);
      smokeTimeoutHandle = 0;
    }

    if (smokeEvaluationTimer) {
      clearTimeout(smokeEvaluationTimer);
      smokeEvaluationTimer = 0;
    }

    smokeTestState.completedAt = new Date().toISOString();
    smokeTestState.ok = Boolean(ok);
    smokeTestState.summary = reason || (ok ? 'Smoke test passed.' : 'Smoke test failed.');
    smokeTestState.shell.snapshot = await collectShellSnapshot();
    smokeTestState.view.snapshot = await collectViewSnapshot();
    smokeTestState.view.currentUrl = mainWindow && !mainWindow.isDestroyed()
      ? mainWindow.webContents.getURL()
      : smokeTestState.view.currentUrl;
    smokeTestState.view.preloadHeartbeat = (() => {
      const viewContentsId = mainWindow && !mainWindow.isDestroyed()
        ? (Number(mainWindow.webContents.id || 0) || 0)
        : 0;
      return viewContentsId > 0
        ? (preloadHeartbeatsByWebContentsId.get(viewContentsId) || null)
        : null;
    })();

    if (
      smokeTestState.view.snapshot?.bodyPreview &&
      isLikelyChromiumErrorText(smokeTestState.view.snapshot.bodyPreview)
    ) {
      addSmokeFailure('Embedded YuChat page rendered a Chromium-style error page.', {
        bodyPreview: smokeTestState.view.snapshot.bodyPreview
      });
      smokeTestState.ok = false;
      if (!reason || ok) {
        smokeTestState.summary = 'Smoke test failed because YuChat showed a browser error page.';
      }
    }

    await captureSmokeScreenshot();

    ensureDirSync(smokeArtifactsDir);
    fs.writeFileSync(smokeReportPath, JSON.stringify(smokeTestState, null, 2));
    appendSmokeLog(`finalize:report-written ok=${Boolean(smokeTestState.ok)} report=${smokeReportPath}`);

    app.exit(smokeTestState.ok ? 0 : 1);
  })();

  return smokeFinalizeInFlight;
}

async function evaluateSmokeTest(trigger) {
  if (!smokeTestState || smokeFinalizeInFlight) return;
  if (!smokeTestState.shell.loaded || !smokeTestState.view.created || !smokeTestState.view.didStartLoading) {
    return;
  }
  if (!smokeTestState.view.domReady && !smokeTestState.view.didFinishLoad && !smokeTestState.view.lastFailLoad) {
    return;
  }

  smokeTestState.shell.snapshot = await collectShellSnapshot();
  smokeTestState.view.snapshot = await collectViewSnapshot();
  smokeTestState.view.currentUrl = mainWindow && !mainWindow.isDestroyed()
    ? mainWindow.webContents.getURL()
    : smokeTestState.view.currentUrl;
  smokeTestState.view.preloadHeartbeat = (() => {
    const viewContentsId = mainWindow && !mainWindow.isDestroyed()
      ? (Number(mainWindow.webContents.id || 0) || 0)
      : 0;
    return viewContentsId > 0
      ? (preloadHeartbeatsByWebContentsId.get(viewContentsId) || null)
      : null;
  })();

  const failures = [];
  const shellSnapshot = smokeTestState.shell.snapshot;
  const viewSnapshot = smokeTestState.view.snapshot;

  if (smokeTestState.view.lastFailLoad) {
    failures.push(
      `BrowserView failed to load ${smokeTestState.view.lastFailLoad.validatedURL || 'the requested page'}: ${smokeTestState.view.lastFailLoad.errorDescription || 'Unknown error'}`
    );
  }

  if (!shellSnapshot || shellSnapshot.error) {
    failures.push('Could not inspect the startup shell UI.');
  } else {
    const shellSignature = normalizeText(`${shellSnapshot.documentTitle || ''} ${shellSnapshot.titleText || ''} ${shellSnapshot.subtitleText || ''}`);
    if (shellSignature && !shellSignature.includes('yuchat')) {
      failures.push('The startup shell did not render the expected YuChat UI.');
    }
  }

  if (!smokeTestState.view.currentUrl || !isTrustedSmokeUrl(smokeTestState.view.currentUrl)) {
    failures.push(`BrowserView ended on an unexpected URL: ${smokeTestState.view.currentUrl || 'empty URL'}`);
  }

  if (!smokeTestState.view.domReady && !smokeTestState.view.didFinishLoad) {
    failures.push('BrowserView never reached a DOM-ready state.');
  }

  if (viewSnapshot?.error) {
    failures.push('Could not inspect the embedded YuChat page.');
  }

  const preloadHeartbeatStage = trimText(smokeTestState.view?.preloadHeartbeat?.stage || '', 120);
  const hasPreloadHeartbeat = Boolean(preloadHeartbeatStage);
  if (!LOCAL_SHELL_REQUESTED && !hasHealthyCustomPreloadMarkers(viewSnapshot) && !hasPreloadHeartbeat) {
    failures.push('Custom preload markers were not detected in the embedded YuChat page.');
  }

  if (isLikelyChromiumErrorText(viewSnapshot?.bodyPreview || '')) {
    failures.push('Embedded YuChat page rendered a Chromium/network error screen.');
  }

  if (failures.length > 0) {
    failures.forEach((failure) => addSmokeFailure(failure));
    await finalizeSmokeTest(false, `Smoke test failed after ${trigger}.`);
    return;
  }

  await finalizeSmokeTest(true, `Smoke test passed after ${trigger}.`);
}

if (smokeTestState) {
  process.on('uncaughtException', (error) => {
    addSmokeFailure('Uncaught exception in the Electron main process.', {
      error: toSerializableError(error)
    });
    void finalizeSmokeTest(false, 'Smoke test aborted because the main process crashed.');
  });

  process.on('unhandledRejection', (error) => {
    addSmokeFailure('Unhandled promise rejection in the Electron main process.', {
      error: toSerializableError(error)
    });
    void finalizeSmokeTest(false, 'Smoke test aborted because of an unhandled rejection.');
  });
}

function getPersistentYuchatSession() {
  return session.fromPartition(YUCHAT_SESSION_PARTITION);
}

function normalizeSessionPreloadPathKey(preloadPath = '') {
  const raw = String(preloadPath || '').trim();
  if (!raw) return '';
  if (/^file:\/\//i.test(raw)) {
    try {
      return path.resolve(new URL(raw).pathname || '');
    } catch {
      return raw.toLowerCase();
    }
  }
  try {
    return path.resolve(raw);
  } catch {
    return raw.toLowerCase();
  }
}

function resolveSessionPreloadScriptPath(entry = null) {
  if (typeof entry === 'string') return entry;
  if (!entry || typeof entry !== 'object') return '';
  if (typeof entry.filePath === 'string') return entry.filePath;
  if (typeof entry.path === 'string') return entry.path;
  return '';
}

function ensureSessionPreloadRegistration(targetSession = null, preloadPath = '', options = {}) {
  if (!targetSession) return false;

  const rawDesiredPath = String(preloadPath || '').trim();
  if (!rawDesiredPath) return false;
  const desiredPathKey = normalizeSessionPreloadPathKey(rawDesiredPath);
  if (!desiredPathKey) return false;

  const supportsModernPreloadApi = (
    typeof targetSession.getPreloadScripts === 'function'
    && typeof targetSession.registerPreloadScript === 'function'
  );

  if (supportsModernPreloadApi) {
    let currentScripts = [];
    try {
      currentScripts = Array.isArray(targetSession.getPreloadScripts())
        ? targetSession.getPreloadScripts()
        : [];
    } catch (error) {
      runtimeWarn('[YuChat] Failed to read session preload scripts:', error);
      return false;
    }

    const hasDesiredPreload = currentScripts.some((entry) => {
      const entryPathKey = normalizeSessionPreloadPathKey(resolveSessionPreloadScriptPath(entry));
      const entryType = String(entry?.type || 'frame').trim().toLowerCase() || 'frame';
      return entryType === 'frame' && entryPathKey === desiredPathKey;
    });
    if (hasDesiredPreload) return true;

    try {
      const registrationId = targetSession.registerPreloadScript({
        type: 'frame',
        filePath: rawDesiredPath
      });
      if (ENABLE_RUNTIME_LOGS) {
        runtimeInfo('[YuChat] Registered preload script in session', {
          source: String(options?.source || 'unknown'),
          preload: rawDesiredPath,
          id: String(registrationId || '')
        });
      }
      return true;
    } catch (error) {
      runtimeWarn('[YuChat] Failed to register preload script in session:', error);
      return false;
    }
  }

  if (
    typeof targetSession.getPreloads !== 'function'
    || typeof targetSession.setPreloads !== 'function'
  ) {
    return false;
  }

  let currentPreloads = [];
  try {
    currentPreloads = Array.isArray(targetSession.getPreloads())
      ? targetSession.getPreloads()
      : [];
  } catch (error) {
    runtimeWarn('[YuChat] Failed to read legacy session preloads:', error);
    return false;
  }

  const hasDesiredLegacyPreload = currentPreloads.some(
    (entry) => normalizeSessionPreloadPathKey(entry) === desiredPathKey
  );
  if (hasDesiredLegacyPreload) return true;

  const mergedPreloads = [...new Set([
    ...currentPreloads
      .map((entry) => String(entry || '').trim())
      .filter(Boolean),
    rawDesiredPath
  ])];

  try {
    targetSession.setPreloads(mergedPreloads);
    if (ENABLE_RUNTIME_LOGS) {
      runtimeInfo('[YuChat] Registered legacy preload in session', {
        source: String(options?.source || 'unknown'),
        preload: rawDesiredPath
      });
    }
    return true;
  } catch (error) {
    runtimeWarn('[YuChat] Failed to register legacy preload in session:', error);
    return false;
  }
}

async function inspectCustomPreloadMarkers(targetContents = null) {
  if (!targetContents || targetContents.isDestroyed()) return null;
  try {
    return await targetContents.executeJavaScript(`(() => {
      const doc = document;
      const root = doc.getElementById('yuchat-full-custom-root');
      const bodyText = String(doc.body?.innerText || doc.body?.textContent || '')
        .replace(/\\s+/g, ' ')
        .trim()
        .slice(0, 2000);
      let customRootVisible = false;
      let customRootChildCount = 0;
      if (root instanceof HTMLElement) {
        customRootChildCount = Number(root.childElementCount || 0) || 0;
        const rect = root.getBoundingClientRect();
        const style = window.getComputedStyle(root);
        customRootVisible = (
          Number(rect?.width || 0) >= 24
          && Number(rect?.height || 0) >= 24
          && style.display !== 'none'
          && style.visibility !== 'hidden'
          && Number(style.opacity || 1) > 0.02
        );
      }
      const rootText = root instanceof HTMLElement
        ? String(root.innerText || root.textContent || '').replace(/\\s+/g, ' ').trim()
        : '';
      const rootInteractiveCount = root instanceof HTMLElement
        ? (Number(root.querySelectorAll('input, button, a, form, [role="button"]').length || 0) || 0)
        : 0;
      return {
        bootstrapMarker: doc.documentElement?.getAttribute('data-yu-bootstrap-preload') || '',
        fullPreloadMarker: doc.documentElement?.getAttribute('data-yu-full-preload') || '',
        hasPrebootStyle: Boolean(doc.getElementById('yuchat-preboot-style')),
        hasCustomStyle: Boolean(doc.getElementById('yuchat-full-custom-style')),
        hasCustomRoot: root instanceof HTMLElement,
        customRootVisible,
        customRootChildCount,
        customRootTextLength: rootText.length,
        customRootInteractiveCount: rootInteractiveCount,
        nativeProfileOpen: doc.body?.classList.contains('yc-native-profile-open') === true,
        bodyTextLength: bodyText.length,
        interactiveCount: Number(doc.querySelectorAll('input, button, a, form, [role="button"]').length || 0) || 0
      };
    })()`, true);
  } catch (error) {
    return {
      error: toSerializableError(error)
    };
  }
}

function hasHealthyCustomPreloadMarkers(snapshot = null) {
  if (!isPlainRecord(snapshot)) return false;
  const bootstrapMarker = trimText(snapshot?.bootstrapMarker || '', 48);
  const fullPreloadMarker = trimText(snapshot?.fullPreloadMarker || '', 48);
  if (snapshot?.nativeProfileOpen === true) {
    const bodyTextLength = Number(snapshot?.bodyTextLength || 0) || 0;
    const interactiveCount = Number(snapshot?.interactiveCount || 0) || 0;
    if (bodyTextLength >= 20 || interactiveCount > 0) {
      return true;
    }
  }
  const customRootChildCount = Number(snapshot?.customRootChildCount || 0) || 0;
  const customRootTextLength = Number(snapshot?.customRootTextLength || 0) || 0;
  const customRootInteractiveCount = Number(snapshot?.customRootInteractiveCount || 0) || 0;
  if (
    snapshot?.hasCustomRoot === true
    && snapshot?.customRootVisible === true
    && customRootChildCount > 0
    && (customRootTextLength >= 20 || customRootInteractiveCount > 0)
  ) {
    return true;
  }
  const bodyTextLength = Number(snapshot?.bodyTextLength || 0) || 0;
  const interactiveCount = Number(snapshot?.interactiveCount || 0) || 0;
  const hasBodySurface = bodyTextLength >= 20 || interactiveCount > 0;
  if (fullPreloadMarker && !/^failed/i.test(fullPreloadMarker) && hasBodySurface) return true;
  if ((/^fallback:/i.test(bootstrapMarker) || /^skipped:/i.test(bootstrapMarker)) && hasBodySurface) return true;
  return false;
}

function hasRenderableBodySurface(snapshot = null) {
  if (!isPlainRecord(snapshot)) return false;
  const bodyTextLength = Number(snapshot?.bodyTextLength || 0) || 0;
  const interactiveCount = Number(snapshot?.interactiveCount || 0) || 0;
  if (bodyTextLength >= 20 || interactiveCount > 0) {
    return true;
  }
  const customRootTextLength = Number(snapshot?.customRootTextLength || 0) || 0;
  const customRootInteractiveCount = Number(snapshot?.customRootInteractiveCount || 0) || 0;
  if (customRootTextLength >= 20 || customRootInteractiveCount > 0) {
    return true;
  }
  return false;
}

function isPreloadHeartbeatReadyStage(stage = '') {
  const normalizedStage = trimText(stage || '', 120).toLowerCase();
  return normalizedStage === 'full:loaded' || normalizedStage === 'bootstrap:loaded';
}

function getRecentPreloadHeartbeat(targetContents = null, maxAgeMs = PRELOAD_HEARTBEAT_GRACE_WINDOW_MS) {
  if (!targetContents || targetContents.isDestroyed()) return null;
  const contentsId = Number(targetContents.id || 0) || 0;
  if (contentsId <= 0) return null;
  const heartbeat = preloadHeartbeatsByWebContentsId.get(contentsId);
  if (!isPlainRecord(heartbeat)) return null;
  const emittedAt = Date.parse(String(heartbeat.at || ''));
  if (!Number.isFinite(emittedAt)) return null;
  const maxAge = Math.max(1000, Number(maxAgeMs || PRELOAD_HEARTBEAT_GRACE_WINDOW_MS) || PRELOAD_HEARTBEAT_GRACE_WINDOW_MS);
  if ((Date.now() - emittedAt) > maxAge) return null;
  return heartbeat;
}

async function ensureMainWindowRenderableSurface(targetContents = null, reason = '') {
  if (!targetContents || targetContents.isDestroyed()) {
    return {
      ok: false,
      skipped: true,
      markersBefore: null,
      markersAfter: null,
      forced: null
    };
  }
  const markersBefore = await inspectCustomPreloadMarkers(targetContents);
  if (hasHealthyCustomPreloadMarkers(markersBefore) || hasRenderableBodySurface(markersBefore)) {
    return {
      ok: true,
      skipped: false,
      markersBefore,
      markersAfter: markersBefore,
      forced: null
    };
  }

  const normalizedReason = trimText(reason || '', 64).toLowerCase();
  const useHeartbeatGrace = (
    normalizedReason === 'startup-probe'
    || normalizedReason === 'progress-stall'
    || normalizedReason === 'global-timeout'
  );
  const recentHeartbeat = useHeartbeatGrace ? getRecentPreloadHeartbeat(targetContents) : null;
  if (recentHeartbeat && isPreloadHeartbeatReadyStage(recentHeartbeat.stage)) {
    return {
      ok: false,
      skipped: true,
      markersBefore,
      markersAfter: markersBefore,
      forced: {
        ok: false,
        reason: 'heartbeat-grace'
      }
    };
  }

  const forced = await forceRevealNativeSurfaceFallback(targetContents, reason);
  await new Promise((resolve) => setTimeout(resolve, 220));
  const markersAfter = await inspectCustomPreloadMarkers(targetContents);
  if (hasHealthyCustomPreloadMarkers(markersAfter) || hasRenderableBodySurface(markersAfter)) {
    return {
      ok: true,
      skipped: false,
      markersBefore,
      markersAfter,
      forced
    };
  }

  if (!LOCAL_SHELL_REQUESTED && !isSmokeTest) {
    const snapshotUrl = trimText(targetContents.getURL() || '', 2200) || YUCHAT_ENTRY_URL;
    if (!/^data:text\/html/i.test(snapshotUrl)) {
      void revealMainWindowLoadFailurePage({
        errorCode: 0,
        errorText: 'Интерфейс загрузился пустым после восстановления.',
        url: snapshotUrl
      });
    }
  }

  return {
    ok: false,
    skipped: false,
    markersBefore,
    markersAfter,
    forced
  };
}

async function forceRevealNativeSurfaceFallback(targetContents = null, reason = '') {
  if (!targetContents || targetContents.isDestroyed()) return null;
  try {
    return await targetContents.executeJavaScript(`(() => {
      const doc = document;
      const html = doc?.documentElement || null;
      const body = doc?.body || null;
      if (!(body instanceof HTMLElement)) return { ok: false, reason: 'no-body' };

      const fullMarker = String(html?.getAttribute('data-yu-full-preload') || '').trim();
      const root = doc.getElementById('yuchat-full-custom-root');
      let hasUsableRoot = false;
      if (root instanceof HTMLElement && root.isConnected && root.childElementCount > 0) {
        const rect = root.getBoundingClientRect();
        const style = window.getComputedStyle(root);
        const rootText = String(root.innerText || root.textContent || '').replace(/\\s+/g, ' ').trim();
        const rootInteractiveCount = Number(root.querySelectorAll('input, button, a, form, [role="button"]').length || 0) || 0;
        hasUsableRoot = (
          Number(rect?.width || 0) >= 24
          && Number(rect?.height || 0) >= 24
          && style.display !== 'none'
          && style.visibility !== 'hidden'
          && Number(style.opacity || 1) > 0.02
          && (rootText.length >= 20 || rootInteractiveCount > 0)
        );
      }
      if (fullMarker || hasUsableRoot) return { ok: false, reason: 'custom-ready' };

      body.classList.add('yc-native-profile-open');
      try {
        html?.setAttribute('data-yu-bootstrap-preload', 'fallback:forced-main');
      } catch {}
      const prebootStyle = doc.getElementById('yuchat-preboot-style');
      if (prebootStyle instanceof HTMLElement) {
        prebootStyle.remove();
      }
      const customStyle = doc.getElementById('yuchat-full-custom-style');
      if (customStyle instanceof HTMLElement && !hasUsableRoot) {
        customStyle.remove();
      }

      const bannerId = 'yuchat-preboot-error-banner';
      if (${ENABLE_PREBOOT_ERROR_BANNERS ? 'false' : 'true'}) {
        const existingBanner = doc.getElementById(bannerId);
        if (existingBanner instanceof HTMLElement) {
          existingBanner.remove();
        }
      } else {
        let banner = doc.getElementById(bannerId);
        if (!(banner instanceof HTMLElement)) {
          banner = doc.createElement('div');
          banner.id = bannerId;
          banner.setAttribute('role', 'alert');
          banner.style.position = 'fixed';
          banner.style.left = '16px';
          banner.style.right = '16px';
          banner.style.top = '16px';
          banner.style.zIndex = '2147483647';
          banner.style.padding = '14px 16px';
          banner.style.borderRadius = '14px';
          banner.style.background = 'rgba(127, 29, 29, 0.96)';
          banner.style.color = '#fff';
          banner.style.font = '600 13px/1.45 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
          banner.style.boxShadow = '0 18px 48px rgba(15, 23, 42, 0.28)';
          body.appendChild(banner);
        }
        banner.textContent = 'Кастомный UI не загрузился, показан базовый экран входа YuChat.';
      }
      return { ok: true, reason: 'native-fallback-forced' };
    })()`, true);
  } catch (error) {
    return {
      ok: false,
      reason: 'execute-failed',
      error: toSerializableError(error)
    };
  }
}

function recordPreloadHeartbeat(event = null, payload = {}) {
  if (!event?.sender || event.sender.isDestroyed()) return;
  const webContentsId = Number(event.sender.id || 0) || 0;
  const normalizedPayload = isPlainRecord(payload) ? payload : {};
  const stage = trimText(normalizedPayload.stage || '', 120);
  if (!stage) return;
  const source = trimText(normalizedPayload.source || '', 120);
  const preloadPath = trimText(normalizedPayload.preloadPath || '', 1024);
  const error = trimText(normalizedPayload.error || '', 320);
  const entry = {
    at: new Date().toISOString(),
    webContentsId,
    stage,
    source,
    ...(preloadPath ? { preloadPath } : {}),
    ...(error ? { error } : {})
  };
  preloadHeartbeatsByWebContentsId.set(webContentsId, entry);
  if (ENABLE_RUNTIME_LOGS) {
    runtimeInfo('[YuChat] Preload heartbeat received', entry);
  }
  if (smokeTestState) {
    recordSmokeEvent('preload-heartbeat', {
      webContentsId,
      stage,
      source,
      ...(preloadPath ? { preloadPath } : {}),
      ...(error ? { error } : {})
    });
    scheduleSmokeEvaluation('preload-heartbeat', 120);
  }
}

async function recoverMissingCustomPreload(targetContents = null, options = {}) {
  if (LOCAL_SHELL_REQUESTED || isSmokeTest) return false;
  if (!targetContents || targetContents.isDestroyed()) return false;

  const currentUrl = trimText(targetContents.getURL() || '', 2200);
  if (!isTrustedSmokeUrl(currentUrl)) return false;

  const markerSnapshot = await inspectCustomPreloadMarkers(targetContents);
  if (hasHealthyCustomPreloadMarkers(markerSnapshot)) {
    return false;
  }

  const freshHeartbeat = getRecentPreloadHeartbeat(targetContents);
  if (freshHeartbeat && isPreloadHeartbeatReadyStage(freshHeartbeat.stage)) {
    runtimeInfo('[YuChat] Preload markers are temporarily missing, but a fresh heartbeat exists. Skipping forced reload.', {
      source: String(options?.source || 'unknown'),
      url: currentUrl,
      heartbeat: freshHeartbeat,
      markers: markerSnapshot
    });
    return false;
  }

  const contentsId = Number(targetContents.id || 0) || 0;
  if (contentsId > 0 && preloadRecoveryAttemptedByContentsId.has(contentsId)) {
    return false;
  }
  if (contentsId > 0) {
    preloadRecoveryAttemptedByContentsId.add(contentsId);
  }

  ensureSessionPreloadRegistration(targetContents.session, WINDOW_PRELOAD_PATH, {
    source: options?.source || 'preload-recovery'
  });

  runtimeWarn('[YuChat] Custom preload markers are missing, forcing one reload.', {
    source: String(options?.source || 'unknown'),
    url: currentUrl,
    markers: markerSnapshot
  });

  try {
    targetContents.reloadIgnoringCache();
  } catch (error) {
    runtimeWarn('[YuChat] Failed to reload renderer for preload recovery:', error);
    return false;
  }
  return true;
}

function encodeAuthStateOriginKey(origin = '') {
  const normalizedOrigin = normalizeAuthStateOrigin(origin);
  if (!normalizedOrigin) return '';
  return Buffer.from(normalizedOrigin, 'utf8')
    .toString('base64')
    .replace(/=+$/g, '')
    .replace(/\+/g, '-')
    .replace(/\//g, '_');
}

function decodeAuthStateOriginKey(originKey = '') {
  const raw = String(originKey || '').trim();
  if (!raw) return '';
  const base64 = raw
    .replace(/-/g, '+')
    .replace(/_/g, '/');
  const paddingLength = base64.length % 4 === 0 ? 0 : (4 - (base64.length % 4));
  const padded = `${base64}${'='.repeat(paddingLength)}`;
  try {
    const decoded = Buffer.from(padded, 'base64').toString('utf8');
    return normalizeAuthStateOrigin(decoded);
  } catch {
    return '';
  }
}

function collectLegacyAuthStateSnapshots(node = null, pathParts = [], result = {}) {
  if (!isPlainRecord(node)) return result;
  const snapshot = normalizeStoredAuthStateSnapshot(node);
  if (hasStoredAuthState(snapshot)) {
    const originCandidate = normalizeAuthStateOrigin(pathParts.join('.'));
    if (originCandidate) {
      result[originCandidate] = {
        localStorage: snapshot.localStorage,
        sessionStorage: snapshot.sessionStorage
      };
    }
    return result;
  }

  Object.entries(node).forEach(([key, value]) => {
    collectLegacyAuthStateSnapshots(value, [...pathParts, String(key || '')], result);
  });
  return result;
}

function getStoredAuthStateRecordByOrigin(origin = '') {
  const normalizedOrigin = normalizeAuthStateOrigin(origin);
  if (!normalizedOrigin) return {};
  const encodedOrigin = encodeAuthStateOriginKey(normalizedOrigin);
  if (encodedOrigin) {
    const byKeySnapshot = normalizeStoredAuthStateSnapshot(
      authStateStore.get(`originsByKey.${encodedOrigin}`) || {}
    );
    if (hasStoredAuthState(byKeySnapshot)) {
      return byKeySnapshot;
    }
  }

  const legacySnapshot = normalizeStoredAuthStateSnapshot(
    authStateStore.get(`origins.${normalizedOrigin}`) || {}
  );
  if (hasStoredAuthState(legacySnapshot)) {
    return legacySnapshot;
  }
  return {};
}

function getStoredAuthStateByOrigin(origin = '') {
  const normalizedOrigin = normalizeAuthStateOrigin(origin);
  if (!normalizedOrigin) return {};
  const normalizedSnapshot = getStoredAuthStateRecordByOrigin(normalizedOrigin);
  const encodedOrigin = encodeAuthStateOriginKey(normalizedOrigin);
  if (encodedOrigin && hasStoredAuthState(normalizedSnapshot)) {
    authStateStore.set(`originsByKey.${encodedOrigin}`, {
      updatedAt: normalizedSnapshot.updatedAt,
      localStorage: normalizedSnapshot.localStorage,
      sessionStorage: normalizedSnapshot.sessionStorage
    });
  }
  return hasStoredAuthState(normalizedSnapshot) ? normalizedSnapshot : {};
}

function setStoredAuthStateByOrigin(origin = '', payload = {}) {
  const normalizedOrigin = normalizeAuthStateOrigin(origin);
  if (!normalizedOrigin) return false;
  const encodedOrigin = encodeAuthStateOriginKey(normalizedOrigin);
  const byKeyPath = encodedOrigin ? `originsByKey.${encodedOrigin}` : '';
  const legacyPath = `origins.${normalizedOrigin}`;

  if (payload?.clear === true) {
    if (byKeyPath) {
      authStateStore.delete(byKeyPath);
    }
    authStateStore.delete(legacyPath);
    return true;
  }

  const currentSnapshot = getStoredAuthStateRecordByOrigin(normalizedOrigin);
  const mergedSnapshot = buildStoredAuthStateSnapshot(currentSnapshot, payload);

  if (hasStoredAuthState(mergedSnapshot)) {
    if (byKeyPath) {
      authStateStore.set(byKeyPath, {
        updatedAt: mergedSnapshot.updatedAt,
        localStorage: mergedSnapshot.localStorage,
        sessionStorage: mergedSnapshot.sessionStorage
      });
    }
    authStateStore.delete(legacyPath);
  } else {
    if (byKeyPath) {
      authStateStore.delete(byKeyPath);
    }
    authStateStore.delete(legacyPath);
  }

  return true;
}

function normalizeSessionCookieSameSite(value = '') {
  const normalized = String(value || '').trim().toLowerCase();
  if (normalized === 'strict') return 'strict';
  if (normalized === 'lax') return 'lax';
  if (normalized === 'no_restriction' || normalized === 'none') return 'no_restriction';
  return 'unspecified';
}

function normalizeSessionCookieSnapshot(cookie = null) {
  if (!isPlainRecord(cookie)) return null;
  const name = String(cookie.name || '').trim().slice(0, 180);
  if (!name) return null;
  const value = typeof cookie.value === 'string' ? cookie.value.slice(0, 8192) : '';
  const domain = String(cookie.domain || '').trim().slice(0, 260);
  const pathValue = String(cookie.path || '/').trim().slice(0, 1024) || '/';
  const path = pathValue.startsWith('/') ? pathValue : `/${pathValue}`;
  const url = String(cookie.url || '').trim().slice(0, 4096);
  const expirationDate = Number(cookie.expirationDate || 0);
  return {
    name,
    value,
    domain,
    path,
    url,
    secure: cookie.secure === true,
    httpOnly: cookie.httpOnly === true,
    hostOnly: cookie.hostOnly === true,
    session: cookie.session === true,
    sameSite: normalizeSessionCookieSameSite(cookie.sameSite),
    expirationDate: Number.isFinite(expirationDate) && expirationDate > 0 ? expirationDate : 0
  };
}

function buildSessionCookieSnapshotKey(cookie = null) {
  const normalized = normalizeSessionCookieSnapshot(cookie);
  if (!normalized) return '';
  return [
    normalized.domain || normalized.url || '',
    normalized.path || '/',
    normalized.name
  ].join('\u001f');
}

function buildCookieUrlFromSnapshot(cookie = null) {
  const normalized = normalizeSessionCookieSnapshot(cookie);
  if (!normalized) return '';
  if (/^https?:\/\//i.test(normalized.url)) {
    return normalized.url;
  }
  const hostname = String(normalized.domain || '').trim().replace(/^\.+/, '');
  if (!hostname) return '';
  return `${normalized.secure ? 'https' : 'http'}://${hostname}${normalized.path || '/'}`;
}

function normalizeStoredYuchatSessionCookies(source = []) {
  const normalizedCookies = [];
  const seen = new Set();
  (Array.isArray(source) ? source : []).forEach((cookie) => {
    if (normalizedCookies.length >= 4000) return;
    const normalized = normalizeSessionCookieSnapshot(cookie);
    if (!normalized) return;
    if (normalized.expirationDate > 0 && normalized.expirationDate <= (Date.now() / 1000)) {
      return;
    }
    const key = buildSessionCookieSnapshotKey(normalized);
    if (!key || seen.has(key)) return;
    seen.add(key);
    normalizedCookies.push(normalized);
  });
  return normalizedCookies;
}

function getStoredYuchatSessionCookies() {
  return normalizeStoredYuchatSessionCookies(
    authStateStore.get(YUCHAT_SESSION_COOKIE_STORE_KEY) || []
  );
}

function setStoredYuchatSessionCookies(source = []) {
  const normalizedCookies = normalizeStoredYuchatSessionCookies(source);
  if (normalizedCookies.length > 0) {
    authStateStore.set(YUCHAT_SESSION_COOKIE_STORE_KEY, normalizedCookies);
  } else {
    authStateStore.delete(YUCHAT_SESSION_COOKIE_STORE_KEY);
  }
  return normalizedCookies;
}

function buildCookieSetPayloadFromSnapshot(cookie = null) {
  const normalized = normalizeSessionCookieSnapshot(cookie);
  if (!normalized) return null;
  const cookieUrl = buildCookieUrlFromSnapshot(normalized);
  if (!cookieUrl) return null;
  const cookiePayload = {
    url: cookieUrl,
    name: normalized.name,
    value: normalized.value,
    path: normalized.path,
    secure: normalized.secure === true,
    httpOnly: normalized.httpOnly === true,
    sameSite: normalizeSessionCookieSameSite(normalized.sameSite)
  };
  if (normalized.domain && normalized.hostOnly !== true) {
    cookiePayload.domain = normalized.domain;
  }
  if (normalized.expirationDate > 0 && normalized.session !== true) {
    cookiePayload.expirationDate = normalized.expirationDate;
  }
  return cookiePayload;
}

async function persistYuchatSessionCookieSnapshot(targetSession = getPersistentYuchatSession()) {
  const rawCookies = await targetSession.cookies.get({}).catch(() => []);
  const cookies = setStoredYuchatSessionCookies(rawCookies);
  return {
    cookieCount: cookies.length
  };
}

async function restorePersistedYuchatSessionCookies(targetSession = getPersistentYuchatSession()) {
  const storedCookies = getStoredYuchatSessionCookies();
  if (!storedCookies.length) {
    return {
      restored: false,
      restoredCount: 0,
      cookieCount: 0
    };
  }

  const currentCookies = normalizeStoredYuchatSessionCookies(
    await targetSession.cookies.get({}).catch(() => [])
  );
  const currentCookieMap = new Map(
    currentCookies.map((cookie) => [buildSessionCookieSnapshotKey(cookie), cookie]).filter(([key]) => Boolean(key))
  );

  let restoredCount = 0;
  for (const cookie of storedCookies) {
    const key = buildSessionCookieSnapshotKey(cookie);
    const currentCookie = key ? currentCookieMap.get(key) : null;
    if (
      currentCookie
      && currentCookie.value === cookie.value
      && currentCookie.expirationDate === cookie.expirationDate
      && currentCookie.secure === cookie.secure
      && currentCookie.httpOnly === cookie.httpOnly
      && currentCookie.sameSite === cookie.sameSite
    ) {
      continue;
    }

    const cookiePayload = buildCookieSetPayloadFromSnapshot(cookie);
    if (!cookiePayload) continue;
    try {
      await targetSession.cookies.set(cookiePayload);
      restoredCount += 1;
    } catch {
      // ignore cookie restore failures for incompatible/expired cookies
    }
  }

  if (restoredCount > 0) {
    yuchatSessionCookiesDirty = true;
    await targetSession.cookies.flushStore().catch(() => {});
  }

  return {
    restored: restoredCount > 0,
    restoredCount,
    cookieCount: storedCookies.length
  };
}

function listStoredAuthStateSnapshots() {
  const result = {};

  const rawOriginsByKey = authStateStore.get('originsByKey') || {};
  if (isPlainRecord(rawOriginsByKey)) {
    Object.entries(rawOriginsByKey).forEach(([originKey, payload]) => {
      const normalizedOrigin = decodeAuthStateOriginKey(originKey);
      if (!normalizedOrigin) return;
      const snapshot = normalizeStoredAuthStateSnapshot(payload);
      if (!hasStoredAuthState(snapshot)) return;
      result[normalizedOrigin] = {
        localStorage: snapshot.localStorage,
        sessionStorage: snapshot.sessionStorage
      };
    });
  }

  const rawLegacyOrigins = authStateStore.get('origins') || {};
  if (!isPlainRecord(rawLegacyOrigins)) {
    return result;
  }
  const legacySnapshots = collectLegacyAuthStateSnapshots(rawLegacyOrigins);
  Object.entries(legacySnapshots).forEach(([origin, snapshot]) => {
    const normalizedOrigin = normalizeAuthStateOrigin(origin);
    if (!normalizedOrigin) return;
    if (Object.prototype.hasOwnProperty.call(result, normalizedOrigin)) return;
    result[normalizedOrigin] = {
      localStorage: snapshot.localStorage,
      sessionStorage: snapshot.sessionStorage
    };
    const encodedOrigin = encodeAuthStateOriginKey(normalizedOrigin);
    if (encodedOrigin) {
      authStateStore.set(`originsByKey.${encodedOrigin}`, {
        updatedAt: Date.now(),
        localStorage: snapshot.localStorage,
        sessionStorage: snapshot.sessionStorage
      });
    }
  });
  return result;
}

async function exportYuchatSessionBackup(event = null, progressPayload = {}) {
  const reportProgress = (ratio = 0, message = '', stage = 'progress') => {
    emitRendererTransferProgressStep(event, progressPayload, ratio, {
      scope: 'backup',
      stage,
      message
    });
  };
  reportProgress(0, 'Читаю cookies', 'start');
  const targetSession = getPersistentYuchatSession();
  const cookies = normalizeStoredYuchatSessionCookies(
    await targetSession.cookies.get({}).catch(() => [])
  );
  reportProgress(0.62, 'Собираю авторизацию');
  const authOrigins = listStoredAuthStateSnapshots();
  reportProgress(1, 'Сессионные данные готовы');
  return {
    partition: YUCHAT_SESSION_PARTITION,
    cookies,
    authOrigins
  };
}

async function importYuchatSessionBackup(snapshotPayload = {}, event = null, progressPayload = {}) {
  const reportProgress = (ratio = 0, message = '', stage = 'progress') => {
    emitRendererTransferProgressStep(event, progressPayload, ratio, {
      scope: 'backup',
      stage,
      message
    });
  };
  const snapshot = isPlainRecord(snapshotPayload) ? snapshotPayload : {};
  reportProgress(0, 'Готовлю восстановление сессии', 'start');
  const targetSession = getPersistentYuchatSession();
  const desiredCookies = Array.isArray(snapshot.cookies)
    ? snapshot.cookies
      .map((cookie) => normalizeSessionCookieSnapshot(cookie))
      .filter(Boolean)
    : [];
  const desiredCookieMap = new Map(
    desiredCookies.map((cookie) => [buildSessionCookieSnapshotKey(cookie), cookie]).filter(([key]) => Boolean(key))
  );

  const currentCookies = await targetSession.cookies.get({}).catch(() => []);
  const currentCookieList = Array.isArray(currentCookies) ? currentCookies : [];
  reportProgress(0.18, 'Удаляю лишние cookies');
  for (let index = 0; index < currentCookieList.length; index += 1) {
    const cookie = currentCookieList[index];
    const key = buildSessionCookieSnapshotKey(cookie);
    if (!key || desiredCookieMap.has(key)) continue;
    const removeUrl = buildCookieUrlFromSnapshot(cookie);
    if (!removeUrl) continue;
    try {
      await targetSession.cookies.remove(removeUrl, String(cookie?.name || '').trim());
    } catch {
      // ignore cookie removal failures during backup restore
    }
    reportProgress(0.18 + (((index + 1) / Math.max(1, currentCookieList.length)) * 0.24), 'Удаляю лишние cookies');
  }

  reportProgress(0.44, 'Восстанавливаю cookies');
  for (let index = 0; index < desiredCookies.length; index += 1) {
    const cookie = desiredCookies[index];
    const cookiePayload = buildCookieSetPayloadFromSnapshot(cookie);
    if (!cookiePayload) continue;
    try {
      await targetSession.cookies.set(cookiePayload);
    } catch {
      // ignore cookie set failures for incompatible/expired cookies
    }
    reportProgress(0.44 + (((index + 1) / Math.max(1, desiredCookies.length)) * 0.28), 'Восстанавливаю cookies');
  }

  const authOrigins = isPlainRecord(snapshot.authOrigins) ? snapshot.authOrigins : {};
  const normalizedAuthOrigins = Object.entries(authOrigins)
    .map(([origin, authSnapshot]) => {
      const normalizedOrigin = normalizeAuthStateOrigin(origin);
      const normalizedSnapshot = normalizeStoredAuthStateSnapshot(authSnapshot);
      if (!normalizedOrigin || !hasStoredAuthState(normalizedSnapshot)) {
        return null;
      }
      return {
        origin: normalizedOrigin,
        snapshot: normalizedSnapshot
      };
    })
    .filter(Boolean);

  const existingAuthOrigins = Object.keys(listStoredAuthStateSnapshots());
  reportProgress(0.78, 'Очищаю авторизацию');
  existingAuthOrigins.forEach((origin, index) => {
    setStoredAuthStateByOrigin(origin, { clear: true });
    reportProgress(0.78 + (((index + 1) / Math.max(1, existingAuthOrigins.length)) * 0.1), 'Очищаю авторизацию');
  });

  reportProgress(0.9, 'Восстанавливаю авторизацию');
  normalizedAuthOrigins.forEach(({ origin, snapshot: authSnapshot }, index) => {
    setStoredAuthStateByOrigin(origin, {
      replace: true,
      pruneMissing: true,
      localStorage: authSnapshot.localStorage,
      sessionStorage: authSnapshot.sessionStorage
    });
    reportProgress(0.9 + (((index + 1) / Math.max(1, normalizedAuthOrigins.length)) * 0.08), 'Восстанавливаю авторизацию');
  });

  reportProgress(0.99, 'Синхронизирую сессию');
  await flushYuchatSessionStorage().catch(() => {});
  reportProgress(1, 'Сессионные данные применены');
  return {
    ok: true,
    cookieCount: desiredCookies.length,
    authOriginCount: normalizedAuthOrigins.length
  };
}

function scheduleYuchatSessionFlush(delay = 350) {
  if (yuchatSessionFlushTimer) {
    clearTimeout(yuchatSessionFlushTimer);
  }

  yuchatSessionFlushTimer = setTimeout(() => {
    yuchatSessionFlushTimer = 0;
    void flushYuchatSessionStorage();
  }, Math.max(0, Number(delay) || 0));
  yuchatSessionFlushTimer.unref?.();
}

async function flushYuchatSessionStorage() {
  if (yuchatSessionFlushTimer) {
    clearTimeout(yuchatSessionFlushTimer);
    yuchatSessionFlushTimer = 0;
  }

  if (yuchatSessionFlushInFlight) {
    return yuchatSessionFlushInFlight;
  }

  const targetSession = getPersistentYuchatSession();
  const shouldPersistCookieSnapshot = yuchatSessionCookiesDirty === true;
  yuchatSessionCookiesDirty = false;
  yuchatSessionFlushInFlight = Promise.allSettled([
    shouldPersistCookieSnapshot
      ? persistYuchatSessionCookieSnapshot(targetSession)
      : Promise.resolve({ cookieCount: getStoredYuchatSessionCookies().length }),
    targetSession.flushStorageData(),
    targetSession.cookies.flushStore()
  ]).finally(() => {
    yuchatSessionFlushInFlight = null;
  });

  return yuchatSessionFlushInFlight;
}

function configureYuchatSession(targetSession = getPersistentYuchatSession()) {
  if (!targetSession) {
    return targetSession;
  }

  ensureSessionPreloadRegistration(targetSession, WINDOW_PRELOAD_PATH, {
    source: 'configureYuchatSession'
  });

  if (configuredYuchatSessions.has(targetSession)) {
    return targetSession;
  }

  configuredYuchatSessions.add(targetSession);
  attachOwaRequestCapture(targetSession);
  targetSession.setPermissionRequestHandler((_webContents, permission, callback, details) => {
    callback(isAllowedRendererPermission(permission, details));
  });
  if (typeof targetSession.setPermissionCheckHandler === 'function') {
    targetSession.setPermissionCheckHandler((_webContents, permission, requestingOrigin, details) => {
      return isAllowedRendererPermission(permission, {
        ...(details && typeof details === 'object' ? details : {}),
        requestingOrigin
      });
    });
  }
  if (typeof targetSession.setDisplayMediaRequestHandler === 'function') {
    try {
      targetSession.setDisplayMediaRequestHandler(async (_request, callback) => {
        try {
          const preferredSource = await getPreferredDesktopCaptureSource();
          if (!preferredSource) {
            callback({});
            return;
          }
          callback({
            video: preferredSource,
            audio: false
          });
        } catch {
          callback({});
        }
      }, {
        useSystemPicker: false
      });
    } catch {
      // ignore display media handler issues
    }
  }

  try {
    targetSession.cookies.on('changed', () => {
      yuchatSessionCookiesDirty = true;
      scheduleYuchatSessionFlush(320);
    });
  } catch {
    // ignore cookie listener issues
  }

  try {
    targetSession.webRequest.onCompleted({
      urls: [
        'https://yuchat.rt.ru/*',
        'https://sso.keyid.rt.ru/*'
      ]
    }, (details = {}) => {
      const resourceType = trimText(details?.resourceType || '', 60).toLowerCase();
      const webContentsId = Number(details?.webContentsId || 0) || 0;
      if (resourceType === 'mainframe' && webContentsId > 0) {
        latestMainFrameStatusByWebContentsId.set(webContentsId, {
          status: Number(details?.statusCode || 0) || 0,
          statusText: trimText(details?.statusLine || '', 180),
          url: trimText(details?.url || '', 2200),
          error: '',
          capturedAt: Date.now()
        });
      }
      scheduleYuchatSessionFlush(240);
    });
  } catch {
    // ignore request listener issues
  }

  try {
    targetSession.webRequest.onErrorOccurred({
      urls: [
        'https://yuchat.rt.ru/*',
        'https://sso.keyid.rt.ru/*'
      ]
    }, (details = {}) => {
      const resourceType = trimText(details?.resourceType || '', 60).toLowerCase();
      const webContentsId = Number(details?.webContentsId || 0) || 0;
      if (resourceType === 'mainframe' && webContentsId > 0) {
        latestMainFrameStatusByWebContentsId.set(webContentsId, {
          status: 0,
          statusText: '',
          url: trimText(details?.url || '', 2200),
          error: trimText(details?.error || '', 220),
          capturedAt: Date.now()
        });
      }
    });
  } catch {
    // ignore request listener issues
  }

  if (ENABLE_DIAGNOSTICS_CAPTURE && !diagnosticCaptureSessions.has(targetSession)) {
    diagnosticCaptureSessions.add(targetSession);
    try {
      targetSession.webRequest.onBeforeRequest({ urls: ['*://*/*'] }, (details, callback) => {
        try {
          const entry = getOrCreateDiagnosticsRequestEntry(details);
          if (entry) {
            const startedAtMs = normalizeDiagnosticsTimestampMs(details?.timestamp);
            entry.url = trimText(details?.url || entry.url, 8192);
            entry.method = trimText((details?.method || entry.method || 'GET').toUpperCase(), 24) || 'GET';
            entry.resourceType = trimText(details?.resourceType || entry.resourceType || 'other', 40) || 'other';
            entry.startedAtMs = Math.min(entry.startedAtMs, startedAtMs);
            entry.startedDateTime = new Date(entry.startedAtMs).toISOString();
            entry.requestBodySize = Math.max(entry.requestBodySize, estimateUploadDataSizeBytes(details));
            scheduleDiagnosticsFlush();
          }
        } finally {
          if (typeof callback === 'function') {
            callback({ cancel: false });
          }
        }
      });

      targetSession.webRequest.onBeforeSendHeaders({ urls: ['*://*/*'] }, (details, callback) => {
        try {
          const entry = getOrCreateDiagnosticsRequestEntry(details);
          if (entry) {
            entry.requestHeaders = normalizeHeaderPairs(details?.requestHeaders || {});
            scheduleDiagnosticsFlush();
          }
        } finally {
          if (typeof callback === 'function') {
            callback({
              cancel: false,
              requestHeaders: details?.requestHeaders || {}
            });
          }
        }
      });

      targetSession.webRequest.onHeadersReceived({ urls: ['*://*/*'] }, (details, callback) => {
        try {
          const entry = getOrCreateDiagnosticsRequestEntry(details);
          if (entry) {
            entry.responseHeaders = normalizeHeaderPairs(details?.responseHeaders || {});
            entry.status = Number(details?.statusCode || entry.status) || 0;
            entry.statusText = trimText(details?.statusLine || entry.statusText, 600);
            scheduleDiagnosticsFlush();
          }
        } finally {
          if (typeof callback === 'function') {
            callback({
              cancel: false,
              responseHeaders: details?.responseHeaders || {}
            });
          }
        }
      });

      targetSession.webRequest.onCompleted({ urls: ['*://*/*'] }, (details) => {
        const responseHeaders = normalizeHeaderPairs(details?.responseHeaders || {});
        finalizeDiagnosticsRequest(details, {
          responseHeaders,
          responseBodySize: Number(details?.encodedDataLength || 0) || 0,
          status: Number(details?.statusCode || 0) || 0,
          statusText: trimText(details?.statusLine || '', 600)
        });
        scheduleDiagnosticsFlush(300);
      });

      targetSession.webRequest.onErrorOccurred({ urls: ['*://*/*'] }, (details) => {
        finalizeDiagnosticsRequest(details, {
          status: 0,
          error: trimText(details?.error || 'Request failed', 1200)
        });
        scheduleDiagnosticsFlush(300);
      });
    } catch (error) {
      runtimeWarn('[YuChat] Failed to install diagnostics network capture:', error);
    }
  }

  return targetSession;
}

function installDiagnosticsForWebContents(targetContents = null) {
  if (!ENABLE_DIAGNOSTICS_CAPTURE || !targetContents || targetContents.isDestroyed()) {
    return;
  }
  if (diagnosticCaptureWebContents.has(targetContents)) {
    return;
  }
  diagnosticCaptureWebContents.add(targetContents);

  const webContentsId = Number(targetContents.id || 0) || 0;
  appendDiagnosticsConsoleEntry({
    level: 'info',
    event: 'diagnostics.init',
    message: `Diagnostics capture enabled for webContents ${webContentsId}`,
    webContentsId
  });
  scheduleDiagnosticsFlush(200);

  targetContents.on('console-message', (_event, level, message, line, sourceId) => {
    appendDiagnosticsConsoleEntry({
      level,
      message,
      line,
      sourceId,
      event: 'renderer.console',
      webContentsId
    });
    scheduleDiagnosticsFlush();
  });

  targetContents.on('render-process-gone', (_event, details) => {
    appendDiagnosticsConsoleEntry({
      level: 'error',
      message: `Renderer process gone: ${JSON.stringify(details || {})}`,
      event: 'renderer.process-gone',
      webContentsId
    });
    flushDiagnosticsArtifacts({ includePending: true });
  });

  targetContents.on('did-fail-load', (_event, errorCode, errorDescription, validatedURL, isMainFrame) => {
    appendDiagnosticsConsoleEntry({
      level: 'warning',
      message: `did-fail-load ${errorCode}: ${errorDescription} (${validatedURL || 'unknown URL'})`,
      event: isMainFrame ? 'renderer.fail-load.main' : 'renderer.fail-load.subframe',
      webContentsId
    });
    scheduleDiagnosticsFlush(200);
  });

  targetContents.on('did-navigate', (_event, url) => {
    appendDiagnosticsConsoleEntry({
      level: 'info',
      message: `did-navigate ${url || ''}`,
      event: 'renderer.did-navigate',
      webContentsId
    });
    scheduleDiagnosticsFlush(200);
  });

  targetContents.on('dom-ready', () => {
    const clickProbeScript = `
      (() => {
        if (window.__yuDiagClickProbeInstalled) return true;
        window.__yuDiagClickProbeInstalled = true;
        if (String(location.protocol || '').toLowerCase().startsWith('devtools:')) {
          return true;
        }

        const describeNode = (node) => {
          if (!(node instanceof Element)) return 'n/a';
          const parts = [String(node.tagName || '').toLowerCase()];
          if (node.id) parts.push('#' + String(node.id));
          const className = String(node.className || '').trim().split(/\\s+/).filter(Boolean).slice(0, 3);
          if (className.length) {
            parts.push('.' + className.join('.'));
          }
          const role = node.getAttribute?.('data-role') || node.getAttribute?.('role') || '';
          if (role) parts.push('[role=' + role + ']');
          return parts.join('');
        };

        const emit = (type, event) => {
          const x = Number(event?.clientX || 0);
          const y = Number(event?.clientY || 0);
          const stack = (typeof document.elementsFromPoint === 'function'
            ? document.elementsFromPoint(x, y)
            : []
          ).slice(0, 7).map((item) => describeNode(item));

          const payload = {
            at: new Date().toISOString(),
            type,
            x,
            y,
            target: describeNode(event?.target),
            stack
          };
          console.debug('[YU_DIAG_CLICK]', JSON.stringify(payload));
        };

        const isVisible = (node) => {
          if (!(node instanceof Element)) return false;
          const rect = node.getBoundingClientRect();
          if (!rect || rect.width < 6 || rect.height < 6) return false;
          if (rect.bottom <= 0 || rect.right <= 0 || rect.top >= window.innerHeight || rect.left >= window.innerWidth) {
            return false;
          }
          const style = window.getComputedStyle(node);
          if (!style) return true;
          return (
            style.display !== 'none'
            && style.visibility !== 'hidden'
            && style.pointerEvents !== 'none'
            && Number(style.opacity || 1) > 0.02
          );
        };

        const probeHitMap = () => {
          const candidates = Array.from(document.querySelectorAll(
            'button, [role="button"], a[href], input, textarea, [data-role]'
          )).filter((node) => {
            if (!(node instanceof Element)) return false;
            if (!isVisible(node)) return false;
            if (!node.closest('#yuchat-full-custom-root')) return false;
            return true;
          }).slice(0, 420);
          const blocked = [];

          candidates.forEach((node) => {
            const rect = node.getBoundingClientRect();
            const cx = Math.min(window.innerWidth - 2, Math.max(1, Math.round(rect.left + (rect.width / 2))));
            const cy = Math.min(window.innerHeight - 2, Math.max(1, Math.round(rect.top + (rect.height / 2))));
            const topNode = document.elementFromPoint(cx, cy);
            const isReachable = (
              topNode === node
              || (topNode instanceof Element && node.contains(topNode))
              || (topNode instanceof Element && topNode.contains(node))
            );
            if (isReachable) return;
            blocked.push({
              target: describeNode(node),
              top: describeNode(topNode),
              x: cx,
              y: cy
            });
          });

          const payload = {
            at: new Date().toISOString(),
            candidates: candidates.length,
            blockedCount: blocked.length,
            blocked: blocked.slice(0, 80)
          };
          if (blocked.length) {
            console.warn('[YU_DIAG_HITTEST]', JSON.stringify(payload));
          } else {
            console.info('[YU_DIAG_HITTEST_OK]', JSON.stringify(payload));
          }
        };

        document.addEventListener('pointerdown', (event) => emit('pointerdown', event), true);
        document.addEventListener('click', (event) => emit('click', event), true);
        console.info('[YU_DIAG] click probe installed');
        setTimeout(probeHitMap, 1200);
        setTimeout(probeHitMap, 3000);
        setTimeout(probeHitMap, 5200);
        const probeInterval = setInterval(probeHitMap, 3000);
        setTimeout(() => clearInterval(probeInterval), 120000);
        return true;
      })()
    `;

    targetContents.executeJavaScript(clickProbeScript, true).catch((error) => {
      appendDiagnosticsConsoleEntry({
        level: 'warning',
        message: `Failed to inject click probe: ${String(error?.message || error || 'unknown')}`,
        event: 'renderer.click-probe.inject-failed',
        webContentsId
      });
      scheduleDiagnosticsFlush(200);
    });
  });
}

function isSafeExternalUrl(targetUrl = '') {
  try {
    const parsed = new URL(targetUrl);
    if (parsed.protocol === 'mailto:') {
      return Boolean(String(parsed.pathname || '').trim());
    }
    return (
      (parsed.protocol === 'http:' || parsed.protocol === 'https:')
      && !/^localhost$/i.test(parsed.hostname)
      && parsed.hostname !== '127.0.0.1'
      && parsed.hostname !== '0.0.0.0'
    );
  } catch {
    return false;
  }
}

function sanitizeOpenFileName(value = '', fallback = 'attachment.bin') {
  const source = String(value || '').trim();
  const baseName = source
    .replace(/[\u0000-\u001f\u007f]/g, '')
    .split(/[\\/]/)
    .pop() || '';
  const safeName = baseName
    .replace(/[<>:"/\\|?*]/g, '_')
    .replace(/\s+/g, ' ')
    .trim()
    .replace(/^\.+/, '')
    .slice(0, 180);
  return safeName || fallback;
}

function getFileNameFromContentDisposition(headerValue = '') {
  const source = String(headerValue || '').trim();
  if (!source) return '';

  const utf8Match = source.match(/filename\*\s*=\s*([^;]+)/i);
  if (utf8Match) {
    const token = String(utf8Match[1] || '').trim().replace(/^"(.*)"$/, '$1');
    const encodedPart = token.includes("''")
      ? token.slice(token.indexOf("''") + 2)
      : token.replace(/^utf-8''/i, '');
    try {
      return decodeURIComponent(encodedPart);
    } catch {
      return encodedPart;
    }
  }

  const quotedMatch = source.match(/filename\s*=\s*"([^"]+)"/i);
  if (quotedMatch) {
    return String(quotedMatch[1] || '').trim();
  }

  const plainMatch = source.match(/filename\s*=\s*([^;]+)/i);
  if (plainMatch) {
    return String(plainMatch[1] || '').trim().replace(/^"(.*)"$/, '$1');
  }

  return '';
}

function getFileExtensionByContentType(contentType = '') {
  const normalized = String(contentType || '').toLowerCase().split(';')[0].trim();
  const map = {
    'application/pdf': '.pdf',
    'application/msword': '.doc',
    'application/vnd.openxmlformats-officedocument.wordprocessingml.document': '.docx',
    'application/vnd.ms-excel': '.xls',
    'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet': '.xlsx',
    'application/vnd.ms-powerpoint': '.ppt',
    'application/vnd.openxmlformats-officedocument.presentationml.presentation': '.pptx',
    'text/plain': '.txt',
    'text/csv': '.csv',
    'application/json': '.json',
    'image/jpeg': '.jpg',
    'image/png': '.png',
    'image/gif': '.gif',
    'image/webp': '.webp',
    'video/mp4': '.mp4',
    'video/webm': '.webm',
    'video/quicktime': '.mov',
    'video/x-matroska': '.mkv',
    'video/x-msvideo': '.avi',
    'video/x-ms-wmv': '.wmv',
    'video/x-ms-asf': '.asf',
    'video/x-flv': '.flv',
    'video/ogg': '.ogv',
    'video/mpeg': '.mpg',
    'video/mp2t': '.ts',
    'video/3gpp': '.3gp',
    'video/3gpp2': '.3g2',
    'application/mp4': '.mp4',
    'audio/mp4': '.m4a',
    'audio/x-m4a': '.m4a',
    'audio/webm': '.webm',
    'audio/aac': '.aac',
    'audio/mpeg': '.mp3',
    'audio/ogg': '.ogg',
    'audio/wav': '.wav'
  };
  return map[normalized] || '';
}

function normalizeContentTypeToken(value = '') {
  return trimText(value || '', 180).toLowerCase().split(';')[0].trim();
}

function shouldPreferExpectedAttachmentContentType(expectedMimeType = '', actualMimeType = '') {
  const expected = normalizeContentTypeToken(expectedMimeType);
  const actual = normalizeContentTypeToken(actualMimeType);
  if (!expected || !actual || expected === actual) {
    return false;
  }
  if (!/^audio\//.test(expected)) {
    return false;
  }
  if (actual === 'application/octet-stream' || actual === 'binary/octet-stream') {
    return true;
  }
  if (expected === 'audio/mp4' && /^(video\/mp4|application\/mp4)$/.test(actual)) {
    return true;
  }
  if (expected === 'audio/webm' && /^video\/webm$/.test(actual)) {
    return true;
  }
  if (expected === 'audio/ogg' && /^application\/ogg$/.test(actual)) {
    return true;
  }
  return false;
}

function resolveFetchedAttachmentContentType(contentType = '', options = {}) {
  const expectedMimeType = normalizeContentTypeToken(options?.expectedMimeType || '');
  const actualMimeType = normalizeContentTypeToken(contentType || '');
  if (shouldPreferExpectedAttachmentContentType(expectedMimeType, actualMimeType)) {
    return expectedMimeType;
  }
  return actualMimeType || expectedMimeType || 'application/octet-stream';
}

function buildTempOpenFilePath(fileName = 'attachment.bin') {
  const tempDir = path.join(app.getPath('temp'), YUCHAT_STORAGE_PROFILE_NAME, 'open-files');
  ensureDirSync(tempDir);
  const safeName = sanitizeOpenFileName(fileName, 'attachment.bin');
  const extension = path.extname(safeName);
  const baseName = path.basename(safeName, extension).slice(0, 120) || 'attachment';
  const suffix = `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  return path.join(tempDir, `${baseName}-${suffix}${extension}`);
}

function buildTempPreviewFilePath(fileName = 'attachment.bin') {
  const tempDir = path.join(app.getPath('temp'), YUCHAT_STORAGE_PROFILE_NAME, 'preview-files');
  ensureDirSync(tempDir);
  const safeName = sanitizeOpenFileName(fileName, 'attachment.bin');
  const extension = path.extname(safeName);
  const baseName = path.basename(safeName, extension).slice(0, 120) || 'attachment';
  const suffix = `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  return path.join(tempDir, `${baseName}-${suffix}${extension}`);
}

function getFavoritesFilesDir() {
  const dir = path.join(app.getPath('userData'), 'favorites-files');
  ensureDirSync(dir);
  return dir;
}

function normalizeFavoritesFileId(value = '') {
  return String(value || '').trim().replace(/[^a-z0-9_-]+/gi, '').slice(0, 80);
}

function buildFavoritesFileUrl(fileId = '', fileName = 'attachment.bin', contentType = '') {
  const safeId = normalizeFavoritesFileId(fileId);
  const safeName = sanitizeOpenFileName(fileName, 'attachment.bin');
  if (!safeId || !safeName) return '';
  const baseUrl = `${LOCAL_ASSET_PROTOCOL}://favorites/${encodeURIComponent(safeId)}/${encodeURIComponent(safeName)}`;
  const safeContentType = normalizeContentTypeToken(contentType || '');
  if (/^(?:image|audio|video)\//i.test(safeContentType)) {
    return `${baseUrl}?contentType=${encodeURIComponent(safeContentType)}`;
  }
  return baseUrl;
}

function resolveFavoritesFilePath(fileId = '', fileName = '') {
  const safeId = normalizeFavoritesFileId(fileId);
  const safeName = sanitizeOpenFileName(fileName || 'attachment.bin', 'attachment.bin');
  if (!safeId || !safeName) return '';
  const dir = path.join(getFavoritesFilesDir(), safeId);
  const filePath = path.join(dir, safeName);
  const root = path.resolve(getFavoritesFilesDir());
  const resolved = path.resolve(filePath);
  if (!resolved.startsWith(`${root}${path.sep}`)) return '';
  return resolved;
}

async function storeFavoritesFile(event, payload = {}) {
  const rawName = String(payload?.fileName || payload?.name || `attachment-${Date.now()}`).trim();
  const safeName = sanitizeOpenFileName(rawName, 'attachment.bin');
  const rawMimeType = normalizeContentTypeToken(payload?.mimeType || payload?.type || '') || 'application/octet-stream';
  const rawBytes = payload?.bytes;
  let body = null;

  if (rawBytes instanceof ArrayBuffer) {
    body = Buffer.from(rawBytes);
  } else if (ArrayBuffer.isView(rawBytes)) {
    body = Buffer.from(rawBytes.buffer, rawBytes.byteOffset, rawBytes.byteLength);
  } else if (Array.isArray(rawBytes)) {
    body = Buffer.from(rawBytes);
  } else if (typeof payload?.base64 === 'string' && payload.base64.trim()) {
    body = Buffer.from(payload.base64.trim(), 'base64');
  }

  if (!body || !body.length) {
    return { ok: false, error: 'Файл пустой' };
  }

  const fileId = normalizeFavoritesFileId(
    payload?.fileId
    || `fav-${Date.now()}-${Math.random().toString(36).slice(2, 10)}`
  );
  const filePath = resolveFavoritesFilePath(fileId, safeName);
  if (!fileId || !filePath) {
    return { ok: false, error: 'Некорректное имя файла' };
  }

  try {
    ensureDirSync(path.dirname(filePath));
    fs.writeFileSync(filePath, body);
    return {
      ok: true,
      fileId,
      fileName: safeName,
      filePath,
      url: buildFavoritesFileUrl(fileId, safeName, rawMimeType),
      mimeType: rawMimeType,
      size: body.length
    };
  } catch (error) {
    return {
      ok: false,
      error: String(error?.message || 'Не удалось сохранить файл в Избранное')
    };
  }
}

function buildAttachmentPreviewCacheKey(payload = {}) {
  const targetUrl = String(payload?.url || '').trim();
  const fileId = String(payload?.fileId || '').trim();
  const fileName = String(payload?.fileName || '').trim();
  return `${targetUrl}::${fileId}::${fileName}`;
}

function buildAttachmentPreviewUrl(token = '', fileName = 'attachment.bin') {
  const safeToken = String(token || '').trim();
  if (!safeToken) return '';
  const safeName = sanitizeOpenFileName(fileName, 'attachment.bin');
  return `${LOCAL_ASSET_PROTOCOL}://preview/${encodeURIComponent(safeToken)}/${encodeURIComponent(safeName)}`;
}

function parseFavoritesFileRefFromUrl(targetUrl = '') {
  const normalizedUrl = String(targetUrl || '').trim();
  if (!normalizedUrl) return null;
  try {
    const parsedUrl = new URL(normalizedUrl);
    if (parsedUrl.protocol !== `${LOCAL_ASSET_PROTOCOL}:`) return null;
    if (String(parsedUrl.host || '').trim().toLowerCase() !== 'favorites') return null;
    const [fileId = '', fileName = 'attachment.bin'] = parsedUrl.pathname
      .split('/')
      .filter(Boolean)
      .map((segment) => decodeURIComponent(segment));
    return {
      fileId: normalizeFavoritesFileId(fileId),
      fileName: sanitizeOpenFileName(fileName, 'attachment.bin')
    };
  } catch {
    return null;
  }
}

function getFavoritesPlayableVideoCacheDir(fileId = '') {
  const safeId = normalizeFavoritesFileId(fileId);
  const dir = path.join(app.getPath('userData'), 'favorites-video-cache', safeId || 'misc');
  ensureDirSync(dir);
  return dir;
}

function buildFavoritesPlayableVideoCacheRecord(fileId = '', fileName = '', sourcePath = '') {
  const safeId = normalizeFavoritesFileId(fileId);
  const safeName = sanitizeOpenFileName(fileName || path.basename(sourcePath || ''), 'video.mp4');
  if (!safeId || !safeName || !sourcePath || !fs.existsSync(sourcePath)) return null;
  const stat = fs.statSync(sourcePath);
  const signature = crypto
    .createHash('sha1')
    .update(`${safeId}:${safeName}:${stat.size}:${Math.round(Number(stat.mtimeMs || 0))}`)
    .digest('hex')
    .slice(0, 16);
  const baseName = sanitizeOpenFileName(path.basename(safeName, path.extname(safeName)) || 'video', 'video')
    .replace(/\.[^.]+$/u, '')
    .slice(0, 82) || 'video';
  const playableName = `${baseName}-${signature}.mp4`;
  return {
    cacheKey: `favorites-playable-video:${safeId}:${safeName}:${signature}`,
    filePath: path.join(getFavoritesPlayableVideoCacheDir(safeId), playableName),
    fileName: playableName,
    contentType: 'video/mp4'
  };
}

function registerAttachmentPreviewFile(filePath = '', fileName = 'attachment.bin', contentType = '', cacheKey = '') {
  const normalizedPath = String(filePath || '').trim();
  if (!normalizedPath || !fs.existsSync(normalizedPath)) return null;
  const existing = cacheKey ? attachmentPreviewCacheByKey.get(cacheKey) || null : null;
  if (existing?.filePath === normalizedPath && existing?.url) {
    attachmentPreviewTokenToRecord.set(existing.token, existing);
    return existing;
  }
  const token = `preview-${Date.now()}-${Math.random().toString(36).slice(2, 10)}`;
  const safeName = sanitizeOpenFileName(fileName || path.basename(normalizedPath), 'attachment.bin');
  const record = {
    token,
    url: buildAttachmentPreviewUrl(token, safeName),
    filePath: normalizedPath,
    fileName: safeName,
    contentType: normalizeContentTypeToken(contentType || '') || resolveLocalAssetMimeType(normalizedPath),
    createdAt: Date.now()
  };
  attachmentPreviewTokenToRecord.set(token, record);
  if (cacheKey) {
    attachmentPreviewCacheByKey.set(cacheKey, record);
    pruneAttachmentPreviewCache(48);
  }
  return record;
}

function resolveExecutablePath(candidatePath = '') {
  const normalizedPath = String(candidatePath || '').trim();
  if (!normalizedPath) return '';
  const candidates = [normalizedPath];
  if (normalizedPath.includes(`${path.sep}app.asar${path.sep}`)) {
    candidates.push(normalizedPath.replace(`${path.sep}app.asar${path.sep}`, `${path.sep}app.asar.unpacked${path.sep}`));
  }
  return candidates.find((candidate) => {
    try {
      return Boolean(candidate && fs.existsSync(candidate) && fs.statSync(candidate).isFile());
    } catch {
      return false;
    }
  }) || '';
}

function getFfmpegBinaryPath() {
  const candidates = [
    process.env.YUCHAT_FFMPEG_PATH,
    process.env.FFMPEG_PATH,
    bundledFfmpegPath,
    '/opt/homebrew/bin/ffmpeg',
    '/usr/local/bin/ffmpeg',
    '/usr/bin/ffmpeg'
  ];
  for (const candidate of candidates) {
    const resolvedPath = resolveExecutablePath(candidate || '');
    if (!resolvedPath) continue;
    try {
      fs.chmodSync(resolvedPath, 0o755);
    } catch {}
    return resolvedPath;
  }
  return '';
}

async function transcodeVideoToPlayableMp4(sourcePath = '', outputPath = '') {
  const ffmpegPath = getFfmpegBinaryPath();
  if (!ffmpegPath) {
    throw new Error('FFmpeg недоступен для подготовки видео.');
  }
  await runChildProcess(ffmpegPath, [
    '-hide_banner',
    '-loglevel',
    'error',
    '-y',
    '-i',
    sourcePath,
    '-map',
    '0:v:0',
    '-map',
    '0:a?',
    '-c:v',
    'libx264',
    '-preset',
    'veryfast',
    '-crf',
    '23',
    '-pix_fmt',
    'yuv420p',
    '-c:a',
    'aac',
    '-b:a',
    '128k',
    '-movflags',
    '+faststart',
    '-f',
    'mp4',
    outputPath
  ]);
}

async function prepareFavoritesPlayableVideo(event, payload = {}) {
  const refFromUrl = parseFavoritesFileRefFromUrl(payload?.sourceUrl || payload?.url || payload?.downloadUrl || '');
  const fileId = normalizeFavoritesFileId(payload?.fileId || refFromUrl?.fileId || '');
  const fileName = sanitizeOpenFileName(payload?.fileName || payload?.name || refFromUrl?.fileName || 'video.mp4', 'video.mp4');
  const sourcePath = resolveFavoritesFilePath(fileId, fileName);
  if (!fileId || !sourcePath || !fs.existsSync(sourcePath)) {
    return {
      ok: false,
      code: 'FAVORITES_VIDEO_NOT_FOUND',
      error: 'Видео в Избранном не найдено.'
    };
  }

  const cacheRecord = buildFavoritesPlayableVideoCacheRecord(fileId, fileName, sourcePath);
  if (!cacheRecord?.filePath) {
    return {
      ok: false,
      code: 'FAVORITES_VIDEO_CACHE_ERROR',
      error: 'Не удалось подготовить кэш видео.'
    };
  }

  const existingRecord = registerAttachmentPreviewFile(
    cacheRecord.filePath,
    cacheRecord.fileName,
    cacheRecord.contentType,
    cacheRecord.cacheKey
  );
  if (existingRecord?.url && fs.existsSync(cacheRecord.filePath) && fs.statSync(cacheRecord.filePath).size > 0) {
    return {
      ok: true,
      url: existingRecord.url,
      fileName: existingRecord.fileName,
      contentType: existingRecord.contentType,
      cached: true
    };
  }

  const promiseKey = cacheRecord.cacheKey;
  const inFlight = favoritesPlayableVideoPromiseByKey.get(promiseKey);
  if (inFlight instanceof Promise) {
    return inFlight;
  }

  const transcodePromise = (async () => {
    try {
      ensureDirSync(path.dirname(cacheRecord.filePath));
      if (fs.existsSync(cacheRecord.filePath)) {
        try {
          fs.unlinkSync(cacheRecord.filePath);
        } catch {}
      }
      await transcodeVideoToPlayableMp4(sourcePath, cacheRecord.filePath);
      if (!fs.existsSync(cacheRecord.filePath) || fs.statSync(cacheRecord.filePath).size <= 0) {
        throw new Error('Конвертер не создал видеофайл.');
      }
      const record = registerAttachmentPreviewFile(
        cacheRecord.filePath,
        cacheRecord.fileName,
        cacheRecord.contentType,
        cacheRecord.cacheKey
      );
      if (!record?.url) {
        throw new Error('Не удалось зарегистрировать подготовленное видео.');
      }
      return {
        ok: true,
        url: record.url,
        fileName: record.fileName,
        contentType: record.contentType,
        cached: false
      };
    } catch (error) {
      try {
        if (fs.existsSync(cacheRecord.filePath)) {
          fs.unlinkSync(cacheRecord.filePath);
        }
      } catch {}
      return {
        ok: false,
        code: 'FAVORITES_VIDEO_TRANSCODE_FAILED',
        error: String(error?.message || 'Не удалось подготовить видео для просмотра.')
      };
    } finally {
      favoritesPlayableVideoPromiseByKey.delete(promiseKey);
    }
  })();

  favoritesPlayableVideoPromiseByKey.set(promiseKey, transcodePromise);
  return transcodePromise;
}

async function readLocalAssetAttachmentPayload(targetUrl = '', parsedUrl = null, payload = {}) {
  if (!parsedUrl || parsedUrl.protocol !== `${LOCAL_ASSET_PROTOCOL}:`) return null;

  const host = String(parsedUrl.host || '').trim().toLowerCase();
  const pathParts = parsedUrl.pathname
    .split('/')
    .filter(Boolean)
    .map((segment) => decodeURIComponent(segment));
  let filePath = '';
  let fileName = sanitizeOpenFileName(String(payload?.fileName || '').trim(), '');
  let contentType = '';

  if (host === 'telegram') {
    const token = pathParts[0] || '';
    const record = telegramMediaTokenToRecord.get(String(token || '').trim()) || null;
    if (!record) {
      return { ok: false, error: 'Файл Telegram не найден' };
    }
    filePath = await downloadTelegramMediaRecord(record);
    fileName = fileName || sanitizeOpenFileName(record.fileName || path.basename(filePath), 'telegram-file.bin');
    contentType = record.mimeType || resolveLocalAssetRequestMimeType(parsedUrl, filePath);
  } else if (host === 'preview') {
    const token = pathParts[0] || '';
    const record = attachmentPreviewTokenToRecord.get(String(token || '').trim()) || null;
    if (!record?.filePath || !fs.existsSync(record.filePath)) {
      if (record?.token) {
        attachmentPreviewTokenToRecord.delete(record.token);
      }
      return { ok: false, error: 'Локальное превью не найдено' };
    }
    filePath = record.filePath;
    fileName = fileName || sanitizeOpenFileName(pathParts[1] || path.basename(filePath), 'attachment.bin');
    contentType = record.contentType || resolveLocalAssetRequestMimeType(parsedUrl, filePath);
  } else if (host === 'favorites') {
    const [fileId = '', requestedFileName = 'attachment.bin'] = pathParts;
    filePath = resolveFavoritesFilePath(fileId, requestedFileName);
    fileName = fileName || sanitizeOpenFileName(requestedFileName || path.basename(filePath), 'attachment.bin');
    contentType = resolveLocalAssetRequestMimeType(parsedUrl, filePath);
  } else {
    const relativePath = pathParts.join('/');
    filePath = resolveLocalAssetPath(relativePath);
    fileName = fileName || sanitizeOpenFileName(pathParts[pathParts.length - 1] || path.basename(filePath), 'attachment.bin');
    contentType = resolveLocalAssetRequestMimeType(parsedUrl, filePath);
  }

  if (!filePath || !fs.existsSync(filePath)) {
    return { ok: false, error: 'Локальный файл не найден' };
  }

  const fileBuffer = fs.readFileSync(filePath);
  if (!fileBuffer.length) {
    return { ok: false, error: 'Файл пустой' };
  }

  return {
    ok: true,
    mode: 'local',
    targetUrl,
    fileBuffer,
    fileName: fileName || sanitizeOpenFileName(path.basename(filePath), 'attachment.bin'),
    contentType: resolveFetchedAttachmentContentType(contentType, {
      expectedMimeType: payload?.expectedMimeType || ''
    })
  };
}

function pruneAttachmentPreviewCache(maxEntries = 32) {
  while (attachmentPreviewCacheByKey.size > maxEntries) {
    const oldestKey = attachmentPreviewCacheByKey.keys().next().value;
    if (!oldestKey) break;
    const record = attachmentPreviewCacheByKey.get(oldestKey) || null;
    attachmentPreviewCacheByKey.delete(oldestKey);
    if (record?.token) {
      attachmentPreviewTokenToRecord.delete(record.token);
    }
  }
}

function isLikelyVideoFilePath(filePath = '') {
  return /\.(mov|mp4|m4v|webm|avi|mkv|mpv|mpg|mpeg|mpe|m2v|ts|m2ts|mts|3gp|3g2|flv|ogv|wmv|asf)$/i.test(String(filePath || '').trim());
}

function spawnDetachedProcess(command = '', args = []) {
  return new Promise((resolve, reject) => {
    let settled = false;
    try {
      const child = spawn(command, Array.isArray(args) ? args : [], {
        detached: true,
        stdio: 'ignore'
      });
      child.once('error', (error) => {
        if (settled) return;
        settled = true;
        reject(error);
      });
      child.once('spawn', () => {
        if (settled) return;
        settled = true;
        child.unref();
        resolve(true);
      });
    } catch (error) {
      reject(error);
    }
  });
}

async function openFilePathViaSystem(filePath = '') {
  const normalizedPath = String(filePath || '').trim();
  if (!normalizedPath) {
    return 'Не удалось открыть файл через ОС';
  }

  const directError = await shell.openPath(normalizedPath);
  if (!directError) {
    return '';
  }

  let fallbackError = String(directError || '').trim();
  const attempts = [];
  if (process.platform === 'darwin') {
    if (isLikelyVideoFilePath(normalizedPath)) {
      const quickTimeBinaryPath = '/System/Applications/QuickTime Player.app/Contents/MacOS/QuickTime Player';
      if (fs.existsSync(quickTimeBinaryPath)) {
        attempts.push({
          command: quickTimeBinaryPath,
          args: [normalizedPath]
        });
      }
    }
    attempts.push({
      command: 'open',
      args: [normalizedPath]
    });
  }

  for (const attempt of attempts) {
    try {
      await spawnDetachedProcess(attempt.command, attempt.args);
      return '';
    } catch (error) {
      fallbackError = String(error?.message || fallbackError || 'Не удалось открыть файл через ОС');
    }
  }

  return fallbackError || 'Не удалось открыть файл через ОС';
}

function normalizeTransferId(value = '') {
  return String(value || '').trim().slice(0, 160);
}

function normalizeTransferScope(value = '') {
  const normalized = String(value || '').trim().toLowerCase();
  return normalized || 'transfer';
}

function normalizeTransferStage(value = '') {
  const normalized = String(value || '').trim().toLowerCase();
  return normalized || 'progress';
}

function normalizeTransferPercent(value = null) {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) return null;
  return Math.max(0, Math.min(100, Math.round(numeric)));
}

function emitRendererTransferProgress(event, payload = {}, progress = {}) {
  const transferId = normalizeTransferId(payload?.transferId);
  if (!transferId) return;
  const sender = event?.sender;
  if (!sender || sender.isDestroyed?.()) return;

  const message = String(progress?.message || '').trim().slice(0, 220);
  const safePayload = {
    transferId,
    scope: normalizeTransferScope(progress?.scope || payload?.transferScope || payload?.scope || ''),
    stage: normalizeTransferStage(progress?.stage || ''),
    percent: normalizeTransferPercent(progress?.percent),
    loadedBytes: Math.max(0, Number(progress?.loadedBytes || 0) || 0),
    totalBytes: Math.max(0, Number(progress?.totalBytes || 0) || 0),
    done: progress?.done === true,
    ok: progress?.ok !== false,
    error: String(progress?.error || '').trim().slice(0, 220),
    message
  };
  try {
    sender.send('yuchat-transfer-progress', safePayload);
  } catch {
    // ignore renderer notification transport failures
  }
}

function resolveTransferProgressRange(payload = {}) {
  const from = normalizeTransferPercent(payload?.progressFrom);
  const to = normalizeTransferPercent(payload?.progressTo);
  const start = from === null ? 0 : from;
  const end = to === null ? 100 : to;
  return end >= start
    ? { from: start, to: end }
    : { from: end, to: start };
}

function interpolateTransferProgressPercent(payload = {}, ratio = 0) {
  const range = resolveTransferProgressRange(payload);
  const safeRatio = Number.isFinite(Number(ratio))
    ? Math.max(0, Math.min(1, Number(ratio)))
    : 0;
  return Math.round(range.from + ((range.to - range.from) * safeRatio));
}

function emitRendererTransferProgressStep(event, payload = {}, ratio = 0, progress = {}) {
  const explicitPercent = normalizeTransferPercent(progress?.percent);
  emitRendererTransferProgress(event, payload, {
    ...progress,
    percent: explicitPercent === null
      ? interpolateTransferProgressPercent(payload, ratio)
      : explicitPercent
  });
}

async function fetchAttachmentPayload(event, payload = {}, options = {}) {
  const targetUrl = String(payload?.url || '').trim();
  const preferredName = String(payload?.fileName || '').trim();
  const preferredFileId = String(payload?.fileId || '').trim();
  const expectedMimeType = normalizeContentTypeToken(payload?.expectedMimeType || '');
  const authToken = String(payload?.authToken || '').trim();
  const normalizedAuthToken = authToken
    ? (authToken.startsWith('Bearer ') ? authToken : `Bearer ${authToken}`)
    : '';
  const transferScope = normalizeTransferScope(options?.transferScope || payload?.transferScope || payload?.scope || 'download');
  const reportProgress = (progress = {}) => {
    emitRendererTransferProgress(event, payload, {
      scope: transferScope,
      ...progress
    });
  };
  if (!isSafeAttachmentUrl(targetUrl)) {
    reportProgress({
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Некорректная ссылка файла'
    });
    return { ok: false, error: 'Некорректная ссылка файла' };
  }

  let parsedUrl = null;
  try {
    parsedUrl = new URL(targetUrl);
  } catch {
    reportProgress({
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Некорректный URL вложения'
    });
    return { ok: false, error: 'Некорректный URL вложения' };
  }

  const shouldDownloadWithSession = (
    isLocalAssetUrl(targetUrl)
    ||
    isTrustedInAppUrl(targetUrl)
    || /\/api\/(?:file|avatar)\.download\//i.test(parsedUrl.pathname || '')
  );

  if (isLocalAssetUrl(targetUrl)) {
    try {
      reportProgress({
        stage: 'start',
        percent: 0
      });
      const localPayload = await readLocalAssetAttachmentPayload(targetUrl, parsedUrl, payload);
      if (localPayload?.ok) {
        reportProgress({
          stage: 'downloading',
          percent: 100,
          loadedBytes: localPayload.fileBuffer.length,
          totalBytes: localPayload.fileBuffer.length
        });
        return localPayload;
      }
      reportProgress({
        stage: 'error',
        done: true,
        ok: false,
        percent: 100,
        error: localPayload?.error || 'Локальный файл не найден'
      });
      return localPayload || { ok: false, error: 'Локальный файл не найден' };
    } catch (error) {
      const errorText = String(error?.message || 'Не удалось прочитать локальный файл');
      reportProgress({
        stage: 'error',
        done: true,
        ok: false,
        percent: 100,
        error: errorText
      });
      return { ok: false, error: errorText };
    }
  }

  const senderSession = event?.sender?.session || null;
  if ((!senderSession || typeof senderSession.fetch !== 'function') && typeof fetch !== 'function') {
    reportProgress({
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Сессия загрузки недоступна'
    });
    return { ok: false, error: 'Сессия загрузки недоступна' };
  }

  const abortTransferId = normalizeTransferId(payload?.transferId || '');
  const abortController = abortTransferId ? new AbortController() : null;
  if (abortController) {
    registerTransferAbortHandler(abortTransferId, (reason = 'canceled') => {
      abortController.abort(createTransferAbortError(reason));
    });
  }

  try {
    reportProgress({
      stage: 'start',
      percent: 0
    });

    const fetchWithSession = async (url, withAuthHeader = true) => {
      const headers = {};
      if (shouldDownloadWithSession && withAuthHeader && normalizedAuthToken) {
        headers['X-KC-Authorization'] = normalizedAuthToken;
      }
      if (senderSession && typeof senderSession.fetch === 'function') {
        return senderSession.fetch(url, {
          method: 'GET',
          cache: 'no-store',
          headers,
          signal: abortController?.signal
        });
      }
      return fetch(url, {
        method: 'GET',
        cache: 'no-store',
        headers,
        signal: abortController?.signal
      });
    };

    const fallbackUrl = (
      preferredFileId &&
      parsedUrl?.origin &&
      isSafeExternalUrl(parsedUrl.origin)
    ) ? `${parsedUrl.origin}/api/file.download/${encodeURIComponent(preferredFileId)}` : '';
    const requestAttachmentResponse = async (url) => {
      let response = await fetchWithSession(url, true);
      if (shouldDownloadWithSession && normalizedAuthToken && [400, 401, 403].includes(Number(response.status || 0))) {
        response = await fetchWithSession(url, false);
      }
      return response;
    };

    const readAttachmentResponseBuffer = async (response) => {
      let fileBuffer = Buffer.alloc(0);
      const totalBytes = Math.max(0, Number(response.headers?.get?.('content-length') || 0) || 0);
      const responseReader = response.body && typeof response.body.getReader === 'function'
        ? response.body.getReader()
        : null;

      if (responseReader) {
        let loadedBytes = 0;
        const chunks = [];
        reportProgress({
          stage: 'downloading',
          percent: totalBytes > 0 ? 0 : null,
          loadedBytes: 0,
          totalBytes
        });

        while (true) {
          const { done, value } = await responseReader.read();
          if (done) break;
          if (!value) continue;
          const chunk = value instanceof Uint8Array ? Buffer.from(value) : Buffer.from(value || []);
          if (!chunk.length) continue;
          chunks.push(chunk);
          loadedBytes += chunk.length;
          const nextPercent = totalBytes > 0
            ? Math.max(1, Math.min(99, Math.round((loadedBytes / totalBytes) * 100)))
            : null;
          reportProgress({
            stage: 'downloading',
            percent: nextPercent,
            loadedBytes,
            totalBytes
          });
        }

        fileBuffer = Buffer.concat(chunks);
        reportProgress({
          stage: 'downloading',
          percent: 100,
          loadedBytes,
          totalBytes: totalBytes || loadedBytes
        });
      } else {
        fileBuffer = Buffer.from(await response.arrayBuffer());
        reportProgress({
          stage: 'downloading',
          percent: 100,
          loadedBytes: fileBuffer.length,
          totalBytes: totalBytes || fileBuffer.length
        });
      }

      return fileBuffer;
    };

    const fetchUrlPayload = async (url, allowFallback = true) => {
      const response = await requestAttachmentResponse(url);
      if (!response.ok) {
        if (allowFallback && shouldDownloadWithSession && fallbackUrl && fallbackUrl !== url) {
          reportProgress({
            stage: 'retry',
            percent: 0
          });
          return fetchUrlPayload(fallbackUrl, false);
        }
        return { ok: false, error: `Не удалось загрузить файл (${response.status})` };
      }

      const responseUrl = new URL(String(response.url || url || '').trim() || url);
      const contentDisposition = String(response.headers?.get?.('content-disposition') || '').trim();
      const contentType = resolveFetchedAttachmentContentType(
        String(response.headers?.get?.('content-type') || '').trim(),
        { expectedMimeType }
      );
      const headerFileName = getFileNameFromContentDisposition(contentDisposition);
      const urlTail = decodeURIComponent(String(responseUrl.pathname || '').split('/').pop() || '').trim();
      let resolvedName = sanitizeOpenFileName(preferredName || headerFileName || urlTail || 'attachment', 'attachment');
      if (!path.extname(resolvedName)) {
        const extensionByType = getFileExtensionByContentType(contentType);
        if (extensionByType) {
          resolvedName = `${resolvedName}${extensionByType}`;
        }
      }

      try {
        const fileBuffer = await readAttachmentResponseBuffer(response);
        return {
          ok: true,
          mode: shouldDownloadWithSession ? 'session' : 'direct',
          targetUrl: url,
          fileBuffer,
          fileName: resolvedName,
          contentType
        };
      } catch (error) {
        if (allowFallback && shouldDownloadWithSession && fallbackUrl && fallbackUrl !== url) {
          reportProgress({
            stage: 'retry',
            percent: 0
          });
          return fetchUrlPayload(fallbackUrl, false);
        }
        throw error;
      }
    };

    const fetched = await fetchUrlPayload(targetUrl, true);
    if (!fetched?.ok) {
      reportProgress({
        stage: 'error',
        done: true,
        ok: false,
        percent: 100,
        error: fetched?.error || 'Не удалось загрузить файл'
      });
      return fetched;
    }

    return fetched;
  } catch (error) {
    const aborted = abortController?.signal?.aborted === true;
    const abortReason = aborted
      ? normalizeTransferAbortReason(abortController?.signal?.reason?.reason || abortController?.signal?.reason || 'canceled')
      : '';
    const errorText = String(
      aborted
        ? (abortReason === 'paused' ? 'TXT поставлен на паузу.' : 'Подготовка TXT отменена.')
        : (error?.message || 'Не удалось загрузить файл')
    );
    reportProgress({
      stage: aborted ? (abortReason === 'paused' ? 'paused' : 'canceled') : 'error',
      done: true,
      ok: aborted ? true : false,
      percent: 100,
      error: errorText
    });
    return aborted
      ? {
          ok: false,
          code: 'TRANSFER_ABORTED',
          reason: abortReason,
          error: errorText
        }
      : { ok: false, error: errorText };
  } finally {
    if (abortTransferId) {
      unregisterTransferAbortHandler(abortTransferId);
    }
  }
}

async function openAttachmentViaOs(event, payload = {}) {
  const targetUrl = String(payload?.url || '').trim();
  if (!isSafeAttachmentUrl(targetUrl)) {
    emitRendererTransferProgress(event, payload, {
      scope: 'open',
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Некорректная ссылка файла'
    });
    return { ok: false, error: 'Некорректная ссылка файла' };
  }

  let parsedUrl = null;
  try {
    parsedUrl = new URL(targetUrl);
  } catch {
    emitRendererTransferProgress(event, payload, {
      scope: 'open',
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Некорректный URL вложения'
    });
    return { ok: false, error: 'Некорректный URL вложения' };
  }

  const shouldDownloadWithSession = (
    isLocalAssetUrl(targetUrl)
    ||
    isTrustedInAppUrl(targetUrl)
    || /\/api\/(?:file|avatar)\.download\//i.test(parsedUrl.pathname || '')
  );

  if (!shouldDownloadWithSession) {
    try {
      emitRendererTransferProgress(event, payload, {
        scope: 'open',
        stage: 'start',
        percent: 0
      });
      await shell.openExternal(targetUrl);
      emitRendererTransferProgress(event, payload, {
        scope: 'open',
        stage: 'done',
        done: true,
        ok: true,
        percent: 100
      });
      return { ok: true, mode: 'external' };
    } catch (error) {
      const errorText = String(error?.message || 'Не удалось открыть ссылку');
      emitRendererTransferProgress(event, payload, {
        scope: 'open',
        stage: 'error',
        done: true,
        ok: false,
        percent: 100,
        error: errorText
      });
      return { ok: false, error: errorText };
    }
  }

  const fetched = await fetchAttachmentPayload(event, payload, {
    transferScope: 'open'
  });
  if (!fetched?.ok) {
    return fetched;
  }

  try {
    const filePath = buildTempOpenFilePath(fetched.fileName || 'attachment');
    fs.writeFileSync(filePath, fetched.fileBuffer);
    emitRendererTransferProgress(event, payload, {
      scope: 'open',
      stage: 'opening',
      percent: 100,
      loadedBytes: fetched.fileBuffer.length,
      totalBytes: fetched.fileBuffer.length
    });
    const openError = await openFilePathViaSystem(filePath);
    if (openError) {
      const errorText = String(openError || 'Не удалось открыть файл через ОС');
      emitRendererTransferProgress(event, payload, {
        scope: 'open',
        stage: 'error',
        done: true,
        ok: false,
        percent: 100,
        error: errorText
      });
      return { ok: false, error: errorText };
    }
    emitRendererTransferProgress(event, payload, {
      scope: 'open',
      stage: 'done',
      done: true,
      ok: true,
      percent: 100
    });
    return { ok: true, mode: 'downloaded', filePath };
  } catch (error) {
    const errorText = String(error?.message || 'Не удалось открыть файл через ОС');
    emitRendererTransferProgress(event, payload, {
      scope: 'open',
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: errorText
    });
    return { ok: false, error: errorText };
  }
}

async function downloadAttachmentViaOs(event, payload = {}) {
  const fetched = await fetchAttachmentPayload(event, payload, {
    transferScope: 'download'
  });
  if (!fetched?.ok) {
    return fetched;
  }

  const result = await dialog.showSaveDialog(getDialogOwnerWindow(), {
    title: 'Сохранить вложение',
    defaultPath: String(fetched.fileName || 'attachment').trim() || 'attachment'
  });
  if (result.canceled || !result.filePath) {
    emitRendererTransferProgress(event, payload, {
      scope: 'download',
      stage: 'canceled',
      done: true,
      ok: false,
      percent: 100,
      error: 'Сохранение отменено'
    });
    return { ok: true, canceled: true, filePath: '' };
  }

  try {
    fs.writeFileSync(result.filePath, fetched.fileBuffer);
    emitRendererTransferProgress(event, payload, {
      scope: 'download',
      stage: 'done',
      done: true,
      ok: true,
      percent: 100,
      loadedBytes: fetched.fileBuffer.length,
      totalBytes: fetched.fileBuffer.length
    });
    return { ok: true, canceled: false, filePath: result.filePath };
  } catch (error) {
    const errorText = String(error?.message || 'Не удалось скачать файл');
    emitRendererTransferProgress(event, payload, {
      scope: 'download',
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: errorText
    });
    return { ok: false, error: errorText };
  }
}

async function fetchAttachmentDataUrl(event, payload = {}) {
  const fetched = await fetchAttachmentPayload(event, payload, {
    transferScope: 'download'
  });
  if (!fetched?.ok) {
    return fetched;
  }
  const mimeType = String(fetched.contentType || '').trim() || 'application/octet-stream';
  emitRendererTransferProgress(event, payload, {
    scope: 'download',
    stage: 'done',
    done: true,
    ok: true,
    percent: 100,
    loadedBytes: fetched.fileBuffer.length,
    totalBytes: fetched.fileBuffer.length
  });
  return {
    ok: true,
    dataUrl: `data:${mimeType};base64,${Buffer.from(fetched.fileBuffer).toString('base64')}`,
    fileName: fetched.fileName || 'attachment',
    contentType: mimeType
  }
}

async function fetchAttachmentArchiveFile(event, payload = {}) {
  const fetched = await fetchAttachmentPayload(event, payload, {
    transferScope: 'download'
  });
  if (!fetched?.ok) {
    return fetched;
  }
  const mimeType = String(fetched.contentType || '').trim() || 'application/octet-stream';
  emitRendererTransferProgress(event, payload, {
    scope: 'download',
    stage: 'done',
    done: true,
    ok: true,
    percent: 100,
    loadedBytes: fetched.fileBuffer.length,
    totalBytes: fetched.fileBuffer.length
  });
  return {
    ok: true,
    contentsBase64: Buffer.from(fetched.fileBuffer).toString('base64'),
    fileName: fetched.fileName || 'attachment',
    contentType: mimeType,
    size: fetched.fileBuffer.length
  };
}

async function prepareAttachmentPreviewUrl(event, payload = {}) {
  const cacheKey = buildAttachmentPreviewCacheKey(payload);
  const existing = cacheKey ? attachmentPreviewCacheByKey.get(cacheKey) || null : null;
  if (existing?.filePath && fs.existsSync(existing.filePath) && existing?.url) {
    emitRendererTransferProgress(event, payload, {
      scope: 'download',
      stage: 'done',
      done: true,
      ok: true,
      percent: 100,
      cached: true
    });
    return {
      ok: true,
      url: existing.url,
      filePath: existing.filePath,
      fileName: existing.fileName || 'attachment',
      contentType: existing.contentType || resolveLocalAssetMimeType(existing.filePath)
    };
  }

  const fetched = await fetchAttachmentPayload(event, payload, {
    transferScope: 'download'
  });
  if (!fetched?.ok) {
    return fetched;
  }

  try {
    const filePath = buildTempPreviewFilePath(fetched.fileName || 'attachment');
    fs.writeFileSync(filePath, fetched.fileBuffer);
    const token = `preview-${Date.now()}-${Math.random().toString(36).slice(2, 10)}`;
    const fileName = String(fetched.fileName || path.basename(filePath) || 'attachment').trim() || 'attachment';
    const contentType = String(fetched.contentType || '').trim() || resolveLocalAssetMimeType(filePath);
    const url = buildAttachmentPreviewUrl(token, fileName);
    const record = {
      token,
      url,
      filePath,
      fileName,
      contentType,
      createdAt: Date.now()
    };
    attachmentPreviewTokenToRecord.set(token, record);
    if (cacheKey) {
      attachmentPreviewCacheByKey.set(cacheKey, record);
      pruneAttachmentPreviewCache(32);
    }
    emitRendererTransferProgress(event, payload, {
      scope: 'download',
      stage: 'done',
      done: true,
      ok: true,
      percent: 100,
      loadedBytes: fetched.fileBuffer.length,
      totalBytes: fetched.fileBuffer.length
    });
    return {
      ok: true,
      url,
      filePath,
      fileName,
      contentType
    };
  } catch (error) {
    const errorText = String(error?.message || 'Не удалось подготовить видео для просмотра');
    emitRendererTransferProgress(event, payload, {
      scope: 'download',
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: errorText
    });
    return { ok: false, error: errorText };
  }
}

async function uploadBinaryToExternalUrl(event, payload = {}) {
  const targetUrl = String(payload?.url || '').trim();
  const reportUploadProgress = (progress = {}) => {
    emitRendererTransferProgress(event, payload, {
      scope: 'upload',
      ...progress
    });
  };
  if (!isSafeExternalUrl(targetUrl)) {
    reportUploadProgress({
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Invalid upload URL'
    });
    throw new Error('Invalid upload URL');
  }

  const method = String(payload?.method || 'PUT').trim().toUpperCase() || 'PUT';
  const rawHeaders = payload?.headers && typeof payload.headers === 'object' && !Array.isArray(payload.headers)
    ? payload.headers
    : {};
  const headers = {};
  Object.entries(rawHeaders).forEach(([key, value]) => {
    const normalizedKey = String(key || '').trim();
    if (!normalizedKey) {
      return;
    }
    if (value === undefined || value === null) {
      return;
    }
    headers[normalizedKey] = String(value);
  });

  const rawBytes = payload?.bytes;
  let body = null;
  if (rawBytes instanceof ArrayBuffer) {
    body = Buffer.from(rawBytes);
  } else if (ArrayBuffer.isView(rawBytes)) {
    body = Buffer.from(rawBytes.buffer, rawBytes.byteOffset, rawBytes.byteLength);
  } else if (Array.isArray(rawBytes)) {
    body = Buffer.from(rawBytes);
  } else if (typeof payload?.base64 === 'string' && payload.base64.trim()) {
    body = Buffer.from(payload.base64.trim(), 'base64');
  }

  if (!body || !body.length) {
    reportUploadProgress({
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      error: 'Upload payload is empty'
    });
    throw new Error('Upload payload is empty');
  }

  const normalizeUploadFormFields = (source = null) => {
    const fields = {};
    const assign = (rawKey, rawValue) => {
      const key = String(rawKey || '').trim();
      if (!key) return;
      if (Array.isArray(rawValue)) {
        rawValue.forEach((value) => assign(key, value));
        return;
      }
      const value = rawValue === undefined || rawValue === null ? '' : String(rawValue);
      if (!Object.prototype.hasOwnProperty.call(fields, key)) {
        fields[key] = value;
        return;
      }
      if (Array.isArray(fields[key])) {
        fields[key].push(value);
        return;
      }
      fields[key] = [fields[key], value];
    };

    if (Array.isArray(source)) {
      source.forEach((entry) => {
        if (!entry || typeof entry !== 'object') return;
        assign(entry.name || entry.key || entry.field || '', entry.value ?? entry.val ?? '');
      });
      return fields;
    }
    if (source && typeof source === 'object') {
      Object.entries(source).forEach(([key, value]) => assign(key, value));
    }
    return fields;
  };

  const sanitizeUploadHeaders = (sourceHeaders = {}, options = {}) => {
    const blocklist = new Set(['host', 'content-length', 'transfer-encoding', 'connection']);
    if (options.multipart === true) {
      blocklist.add('content-type');
    }
    const normalized = {};
    Object.entries(sourceHeaders || {}).forEach(([rawKey, rawValue]) => {
      const key = String(rawKey || '').trim().toLowerCase();
      if (!key || blocklist.has(key)) return;
      if (rawValue === undefined || rawValue === null) return;
      normalized[key] = String(rawValue);
    });
    return normalized;
  };

  const buildMultipartBody = (fields = {}, fileBuffer = Buffer.alloc(0), meta = {}) => {
    const boundary = `----yuchat-upload-${Date.now().toString(16)}-${Math.random().toString(16).slice(2)}`;
    const chunks = [];
    const pushText = (value = '') => {
      chunks.push(Buffer.from(String(value), 'utf8'));
    };
    const safeHeaderValue = (value = '') => String(value || '').replace(/[\r\n"]/g, '_');

    Object.entries(fields).forEach(([key, value]) => {
      const values = Array.isArray(value) ? value : [value];
      values.forEach((entry) => {
        pushText(`--${boundary}\r\n`);
        pushText(`Content-Disposition: form-data; name="${safeHeaderValue(key)}"\r\n\r\n`);
        pushText(String(entry ?? ''));
        pushText('\r\n');
      });
    });

    const fileFieldName = String(meta.fileFieldName || 'file').trim() || 'file';
    const rawFileName = String(meta.fileName || 'upload.bin').trim() || 'upload.bin';
    const fileName = sanitizeOpenFileName(rawFileName, 'upload.bin');
    const fileType = String(meta.fileType || '').trim() || 'application/octet-stream';

    pushText(`--${boundary}\r\n`);
    pushText(`Content-Disposition: form-data; name="${safeHeaderValue(fileFieldName)}"; filename="${safeHeaderValue(fileName)}"\r\n`);
    pushText(`Content-Type: ${safeHeaderValue(fileType)}\r\n\r\n`);
    chunks.push(fileBuffer);
    pushText('\r\n');
    pushText(`--${boundary}--\r\n`);

    return {
      boundary,
      body: Buffer.concat(chunks)
    };
  };

  const performUploadRequest = (requestUrl = '', requestMethod = 'PUT', requestHeaders = {}, requestBody = Buffer.alloc(0), redirectDepth = 0) => (
    new Promise((resolve, reject) => {
      let parsedUrl = null;
      try {
        parsedUrl = new URL(requestUrl);
      } catch {
        reject(new Error('Invalid upload URL'));
        return;
      }

      const isTls = parsedUrl.protocol === 'https:';
      const transport = isTls ? https : http;
      const options = {
        protocol: parsedUrl.protocol,
        hostname: parsedUrl.hostname,
        port: parsedUrl.port || (isTls ? 443 : 80),
        method: requestMethod,
        path: `${parsedUrl.pathname || '/'}${parsedUrl.search || ''}`,
        headers: requestHeaders
      };

      const req = transport.request(options, (res) => {
        const chunks = [];
        let totalBytes = 0;
        res.on('data', (chunk) => {
          if (!(chunk instanceof Buffer)) return;
          if (totalBytes >= 8192) return;
          const remaining = 8192 - totalBytes;
          const slice = chunk.length > remaining ? chunk.subarray(0, remaining) : chunk;
          chunks.push(slice);
          totalBytes += slice.length;
        });
        res.on('end', () => {
          const status = Number(res.statusCode || 0);
          const locationHeader = String(res.headers?.location || '').trim();
          const isRedirect = [301, 302, 303, 307, 308].includes(status);
          if (isRedirect && locationHeader && redirectDepth < 4) {
            let redirectUrl = '';
            try {
              redirectUrl = new URL(locationHeader, parsedUrl).toString();
            } catch {
              redirectUrl = '';
            }
            if (redirectUrl && isSafeExternalUrl(redirectUrl)) {
              const nextMethod = status === 303 ? 'GET' : requestMethod;
              const nextBody = (nextMethod === 'GET' || nextMethod === 'HEAD') ? Buffer.alloc(0) : requestBody;
              const nextHeaders = { ...requestHeaders };
              if (nextMethod === 'GET' || nextMethod === 'HEAD') {
                delete nextHeaders['content-length'];
                delete nextHeaders['content-type'];
              }
              performUploadRequest(redirectUrl, nextMethod, nextHeaders, nextBody, redirectDepth + 1)
                .then(resolve)
                .catch(reject);
              return;
            }
          }

          const bodySnippet = Buffer.concat(chunks).toString('utf8').trim().slice(0, 400);
          resolve({
            ok: status >= 200 && status < 300,
            status,
            statusText: String(res.statusMessage || '').trim(),
            bodySnippet
          });
        });
      });

      req.on('error', reject);
      req.setTimeout(30000, () => {
        req.destroy(new Error('Upload request timeout'));
      });

      const shouldWriteBody = requestBody.length > 0 && requestMethod !== 'GET' && requestMethod !== 'HEAD';
      const totalBytes = shouldWriteBody ? requestBody.length : 0;

      const waitForDrain = () => (
        new Promise((resolveDrain, rejectDrain) => {
          const handleDrain = () => {
            req.off('error', handleError);
            resolveDrain();
          };
          const handleError = (error) => {
            req.off('drain', handleDrain);
            rejectDrain(error);
          };
          req.once('drain', handleDrain);
          req.once('error', handleError);
        })
      );

      const writeBodyWithProgress = async () => {
        if (!shouldWriteBody) {
          req.end();
          return;
        }
        let sentBytes = 0;
        const chunkSize = 256 * 1024;
        reportUploadProgress({
          stage: 'uploading',
          percent: 0,
          loadedBytes: 0,
          totalBytes
        });
        for (let offset = 0; offset < requestBody.length; offset += chunkSize) {
          const end = Math.min(requestBody.length, offset + chunkSize);
          const chunk = requestBody.subarray(offset, end);
          const canContinue = req.write(chunk);
          sentBytes += chunk.length;
          reportUploadProgress({
            stage: 'uploading',
            percent: sentBytes >= totalBytes
              ? 99
              : Math.max(1, Math.min(99, Math.round((sentBytes / totalBytes) * 100))),
            loadedBytes: sentBytes,
            totalBytes
          });
          if (!canContinue) {
            await waitForDrain();
          }
        }
        req.end();
      };

      void writeBodyWithProgress().catch((error) => {
        req.destroy(error);
      });
    })
  );

  const normalizedFormFields = normalizeUploadFormFields(payload?.formFields);
  const hasFormFields = Object.keys(normalizedFormFields).length > 0;

  let requestBody = body;
  let requestHeaders = sanitizeUploadHeaders(headers, { multipart: hasFormFields });
  if (hasFormFields) {
    const multipart = buildMultipartBody(normalizedFormFields, body, {
      fileFieldName: payload?.fileFieldName,
      fileName: payload?.fileName,
      fileType: payload?.fileType
    });
    requestBody = multipart.body;
    requestHeaders['content-type'] = `multipart/form-data; boundary=${multipart.boundary}`;
  }
  if (!hasFormFields && method === 'PUT' && !Object.prototype.hasOwnProperty.call(requestHeaders, 'content-type')) {
    requestHeaders['content-type'] = 'application/x-www-form-urlencoded';
  }
  requestHeaders['content-length'] = String(requestBody.length);
  requestHeaders.accept = requestHeaders.accept || 'application/json, text/plain, */*';

  reportUploadProgress({
    stage: 'start',
    percent: 0,
    loadedBytes: 0,
    totalBytes: requestBody.length
  });

  try {
    const uploadResult = await performUploadRequest(targetUrl, method, requestHeaders, requestBody, 0);
    if (uploadResult?.ok) {
      reportUploadProgress({
        stage: 'done',
        done: true,
        ok: true,
        percent: 100,
        loadedBytes: requestBody.length,
        totalBytes: requestBody.length
      });
    } else {
      reportUploadProgress({
        stage: 'error',
        done: true,
        ok: false,
        percent: 100,
        loadedBytes: requestBody.length,
        totalBytes: requestBody.length,
        error: uploadResult?.bodySnippet || uploadResult?.statusText || `Upload failed (${uploadResult?.status || 0})`
      });
    }
    return uploadResult;
  } catch (error) {
    const errorText = String(error?.message || 'Upload request failed').trim().slice(0, 400);
    reportUploadProgress({
      stage: 'error',
      done: true,
      ok: false,
      percent: 100,
      loadedBytes: requestBody.length,
      totalBytes: requestBody.length,
      error: errorText
    });
    return {
      ok: false,
      status: 0,
      statusText: '',
      bodySnippet: errorText
    };
  }
}

function isInternalYuChatUrl(targetUrl = '') {
  return isTrustedInAppUrl(targetUrl);
}

function installSystemNavigationHandlers(webContents) {
  webContents.setWindowOpenHandler(({ url = '' }) => {
    const normalizedUrl = String(url || '').trim();
    if (isTrustedInAppUrl(normalizedUrl)) {
      return {
        action: 'allow',
        overrideBrowserWindowOptions: {
          webPreferences: {
            contextIsolation: true,
            partition: YUCHAT_SESSION_PARTITION
          }
        }
      };
    }

    if (isSafeExternalUrl(normalizedUrl)) {
      void shell.openExternal(normalizedUrl);
    }

    return { action: 'deny' };
  });

  webContents.on('will-navigate', (event, url) => {
    if (isTrustedInAppUrl(url)) {
      return;
    }

    event.preventDefault();
    if (isSafeExternalUrl(url)) {
      void shell.openExternal(url);
    }
  });

  webContents.on('before-input-event', (event, input) => {
    if (input.type !== 'keyDown') return;
    const isMod = input.meta || input.control;
    if (!isMod) return;

    const key = String(input.key || '').toLowerCase();
    if (key === 'c') {
      webContents.copy();
      event.preventDefault();
    } else if (key === 'v') {
      webContents.paste();
      event.preventDefault();
    } else if (key === 'x') {
      webContents.cut();
      event.preventDefault();
    } else if (key === 'a') {
      webContents.selectAll();
      event.preventDefault();
    }
  });
}

function normalizeNotificationAuthToken(value = '') {
  const token = String(value || '').trim();
  if (!token) return '';
  return token.startsWith('Bearer ') ? token : `Bearer ${token}`;
}

function normalizeNotificationRemoteIconUrl(value = '') {
  const raw = String(value || '').trim();
  if (!raw) return '';
  if (/^https?:\/\//i.test(raw)) {
    return raw;
  }
  if (/^\/\//.test(raw)) {
    return `https:${raw}`;
  }
  if (raw.startsWith('/')) {
    try {
      return new URL(raw, getYuchatEntryOrigin()).toString();
    } catch {
      return '';
    }
  }
  return '';
}

function getNotificationFetchSession(preferredSession = null) {
  if (preferredSession && typeof preferredSession.fetch === 'function') {
    return preferredSession;
  }
  try {
    const yuchatSession = session.fromPartition(YUCHAT_SESSION_PARTITION);
    if (yuchatSession && typeof yuchatSession.fetch === 'function') {
      return yuchatSession;
    }
  } catch {
    // ignore session resolution failures
  }
  if (session?.defaultSession && typeof session.defaultSession.fetch === 'function') {
    return session.defaultSession;
  }
  return null;
}

async function fetchNotificationRemoteIcon(remoteIconUrl = '', options = {}) {
  const iconUrl = normalizeNotificationRemoteIconUrl(remoteIconUrl);
  if (!iconUrl || !isSafeExternalUrl(iconUrl)) return null;

  const nowAt = Date.now();
  const cached = notificationIconCache.get(iconUrl) || null;
  if (cached && Number(cached.expiresAt || 0) > nowAt) {
    return cached.image || null;
  }

  if (notificationIconPending.has(iconUrl)) {
    return notificationIconPending.get(iconUrl);
  }

  const fetchSession = getNotificationFetchSession(options?.senderSession || null);
  if (!fetchSession || typeof fetchSession.fetch !== 'function') {
    return null;
  }

  const authToken = normalizeNotificationAuthToken(options?.authToken || '');
  const fetchIconPromise = (async () => {
    const requestIcon = async (withAuthHeader = true) => {
      const headers = {};
      if (withAuthHeader && authToken) {
        headers['X-KC-Authorization'] = authToken;
      }
      return fetchSession.fetch(iconUrl, {
        method: 'GET',
        cache: 'no-store',
        headers
      });
    };

    let response = await requestIcon(true);
    if (authToken && (response.status === 401 || response.status === 403)) {
      response = await requestIcon(false);
    }
    if (!response.ok) return null;

    const contentType = String(response.headers?.get?.('content-type') || '').trim();
    if (contentType && !/^image\//i.test(contentType)) {
      return null;
    }
    const buffer = Buffer.from(await response.arrayBuffer());
    if (!buffer.length) return null;
    const mime = /^image\//i.test(contentType) ? contentType : 'image/png';
    const dataUrl = `data:${mime};base64,${buffer.toString('base64')}`;
    if (!(nativeImage?.createFromDataURL)) return null;
    const image = nativeImage.createFromDataURL(dataUrl);
    if (!image || typeof image.isEmpty !== 'function' || image.isEmpty()) {
      return null;
    }
    notificationIconCache.set(iconUrl, {
      image,
      expiresAt: nowAt + NOTIFICATION_ICON_CACHE_TTL_MS
    });
    return image;
  })();

  notificationIconPending.set(iconUrl, fetchIconPromise);
  try {
    return await fetchIconPromise;
  } catch {
    return null;
  } finally {
    notificationIconPending.delete(iconUrl);
  }
}

async function resolveNotificationIcon(payload = {}, options = {}) {
  const fallbackIcon = path.join(__dirname, 'assets', 'icon.png');
  const fallbackLabel = cleanNotificationText(
    payload?.authorName
    || payload?.subtitle
    || payload?.title
    || 'YuChat',
    120
  ) || 'YuChat';
  const generatedFallbackIcon = createNotificationAvatarImage(null, fallbackLabel);
  const iconDataUrl = typeof payload?.iconDataUrl === 'string' ? payload.iconDataUrl.trim() : '';
  if (!iconDataUrl) {
    if (generatedFallbackIcon) {
      return generatedFallbackIcon;
    }
    return fallbackIcon;
  }

  try {
    if (/^data:image\//i.test(iconDataUrl) && nativeImage?.createFromDataURL) {
      const image = nativeImage.createFromDataURL(iconDataUrl);
      const roundedImage = createNotificationAvatarImage(image, fallbackLabel);
      if (roundedImage && typeof roundedImage.isEmpty === 'function' && !roundedImage.isEmpty()) {
        return roundedImage;
      }
    }
  } catch {
    // fallback below
  }

  if (/^file:/i.test(iconDataUrl)) {
    try {
      const image = nativeImage.createFromPath(new URL(iconDataUrl).pathname);
      const roundedImage = createNotificationAvatarImage(image, fallbackLabel);
      if (roundedImage && typeof roundedImage.isEmpty === 'function' && !roundedImage.isEmpty()) {
        return roundedImage;
      }
    } catch {
      // fallback below
    }
  }

  const remoteIcon = await fetchNotificationRemoteIcon(iconDataUrl, {
    senderSession: options?.senderSession || null,
    authToken: options?.authToken || payload?.authToken || ''
  });
  if (remoteIcon) {
    const roundedImage = createNotificationAvatarImage(remoteIcon, fallbackLabel);
    if (roundedImage && typeof roundedImage.isEmpty === 'function' && !roundedImage.isEmpty()) {
      return roundedImage;
    }
  }
  return generatedFallbackIcon || fallbackIcon;
}

function showAppNotification(payload = {}, options = {}) {
  void (async () => {
    if (!Notification.isSupported()) return;
    const workspaceId = String(payload?.workspaceId || '').trim();
    const chatId = String(payload?.chatId || '').trim();
    const source = workspaceId === 'telegram' || /^tg:/i.test(chatId)
      ? 'telegram'
      : 'yuchat';
    if (systemNotificationPreferences[source] === false) return;

    const title = typeof payload.title === 'string' && payload.title.trim()
      ? payload.title.trim()
      : 'YuChat';
    const subtitle = typeof payload.subtitle === 'string' ? payload.subtitle.trim() : '';
    const body = typeof payload.body === 'string' ? payload.body.trim() : '';
    const notificationKey = `${normalizeText(title)}::${normalizeText(subtitle)}::${normalizeText(body)}`;
    const nowAt = Date.now();
    const lastShownAt = Number(recentNotificationKeys.get(notificationKey) || 0);
    if (lastShownAt && nowAt - lastShownAt < 2500) {
      return;
    }
    recentNotificationKeys.set(notificationKey, nowAt);
    recentNotificationKeys.forEach((shownAt, key) => {
      if (nowAt - Number(shownAt || 0) > 25000) {
        recentNotificationKeys.delete(key);
      }
    });

    const icon = await resolveNotificationIcon(payload, options);
    const activationPayload = buildNotificationActivationPayload(payload);
    const notification = new Notification({
      title,
      subtitle,
      body,
      icon,
      silent: true
    });

    activeNotifications.add(notification);
    const releaseNotification = () => {
      activeNotifications.delete(notification);
    };

    notification.on('click', () => {
      if (mainWindow && !mainWindow.isDestroyed()) {
        if (mainWindow.isMinimized()) {
          mainWindow.restore();
        }
        mainWindow.show();
        mainWindow.focus();
        if (activationPayload && mainWindow.webContents && !mainWindow.webContents.isDestroyed()) {
          try {
            mainWindow.webContents.send('yuchat-notification-activate', activationPayload);
          } catch {
            // ignore notification activation delivery failures
          }
        }
      }
      releaseNotification();
    });

    notification.on('close', releaseNotification);
    notification.on('failed', releaseNotification);

    notification.show();
    const releaseTimer = setTimeout(releaseNotification, 15000);
    releaseTimer.unref?.();
  })().catch(() => {
    // ignore notification rendering failures
  });
}

function normalizeChatId(value = '') {
  const raw = String(value || '').trim();
  if (!raw) return '';
  const prefixedMatch = raw.match(/^([a-z]+):(.+)$/i);
  if (!prefixedMatch) return raw;
  const prefix = String(prefixedMatch[1] || '').toLowerCase();
  const id = String(prefixedMatch[2] || '').trim();
  if (!prefix || !id) return '';
  if (['w', 'p', 'u', 't', 'c'].includes(prefix)) {
    return `${prefix}:${id}`;
  }
  return raw;
}

function chatIdsAreEquivalent(left = '', right = '') {
  const leftValue = normalizeChatId(left);
  const rightValue = normalizeChatId(right);
  if (!leftValue || !rightValue) return false;
  if (leftValue === rightValue) return true;
  const leftParts = leftValue.match(/^([a-z]+):(.+)$/i);
  const rightParts = rightValue.match(/^([a-z]+):(.+)$/i);
  if (!leftParts || !rightParts) return false;
  const leftPrefix = leftParts[1].toLowerCase();
  const rightPrefix = rightParts[1].toLowerCase();
  const leftId = leftParts[2];
  const rightId = rightParts[2];
  if (leftId !== rightId) return false;
  return (
    (leftPrefix === 'p' && rightPrefix === 'u')
    || (leftPrefix === 'u' && rightPrefix === 'p')
  );
}

function isUsableWindow(targetWindow = null) {
  return Boolean(targetWindow) && !targetWindow.isDestroyed();
}

function setMainWindowProgressBarValue(_value = -1) {
  // Keep Dock/taskbar progress disabled; splash handles loading feedback visually.
}

function syncStartupTaskProgress(percent = 0) {
  const normalizedPercent = Math.max(0, Math.min(100, Number(percent) || 0));
  if (normalizedPercent <= 0) {
    setMainWindowProgressBarValue(-1);
    return;
  }
  if (normalizedPercent >= 100) {
    setMainWindowProgressBarValue(1);
    return;
  }
  setMainWindowProgressBarValue(Math.max(0.02, Math.min(0.99, normalizedPercent / 100)));
}

function normalizeStartupSplashState(patch = {}, fallback = null) {
  const base = isPlainRecord(fallback) ? fallback : startupSplashState;
  const source = isPlainRecord(patch) ? patch : {};
  const percent = Object.prototype.hasOwnProperty.call(source, 'percent')
    ? Number(source.percent)
    : Number(base?.percent);

  const nextState = {
    percent: Math.max(0, Math.min(100, Math.round(Number.isFinite(percent) ? percent : DEFAULT_STARTUP_SPLASH_STATE.percent))),
    phase: trimText(
      Object.prototype.hasOwnProperty.call(source, 'phase') ? source.phase : base?.phase,
      120
    ).trim(),
    detail: trimText(
      Object.prototype.hasOwnProperty.call(source, 'detail') ? source.detail : base?.detail,
      220
    ).trim()
  };

  if (!nextState.phase) {
    nextState.phase = DEFAULT_STARTUP_SPLASH_STATE.phase;
  }
  if (!nextState.detail) {
    nextState.detail = DEFAULT_STARTUP_SPLASH_STATE.detail;
  }

  return nextState;
}

function syncStartupSplashWindow(force = false) {
  if (!isUsableWindow(startupSplashWindow) || !startupSplashReady) {
    return;
  }
  if (!force && startupSplashClosing) {
    return;
  }

  const serializedState = JSON.stringify(startupSplashState)
    .replace(/</g, '\\u003c')
    .replace(/\u2028/g, '\\u2028')
    .replace(/\u2029/g, '\\u2029');

  startupSplashWindow.webContents.executeJavaScript(
    `window.__updateStartupSplash?.(${serializedState});`,
    true
  ).catch(() => {});
}

function setStartupSplashState(patch = {}) {
  const nextState = normalizeStartupSplashState(patch, startupSplashState);
  if (!startupSplashClosing) {
    nextState.percent = Math.max(Number(startupSplashState?.percent || 0), nextState.percent);
  }
  startupSplashState = nextState;
  syncStartupTaskProgress(startupSplashState.percent);
  syncStartupSplashWindow();
}

function focusStartupSplashWindow() {
  if (!isUsableWindow(startupSplashWindow)) {
    return false;
  }

  if (!startupSplashWindow.isVisible()) {
    startupSplashWindow.show();
  }
  startupSplashWindow.focus();
  return true;
}

function closeStartupSplashWindow(options = {}) {
  if (!isUsableWindow(startupSplashWindow)) {
    startupSplashWindow = null;
    startupSplashReady = false;
    startupSplashClosing = false;
    setMainWindowProgressBarValue(-1);
    return;
  }

  if (startupSplashClosing) {
    return;
  }

  const animated = options?.animated !== false;
  const targetWindow = startupSplashWindow;
  startupSplashClosing = true;
  syncStartupTaskProgress(100);

  const finalizeClose = () => {
    if (startupSplashWindow === targetWindow) {
      startupSplashWindow = null;
    }
    startupSplashReady = false;
    startupSplashClosing = false;
    if (isUsableWindow(targetWindow)) {
      try {
        targetWindow.destroy();
      } catch {
        // ignore splash teardown failures
      }
    }
    setMainWindowProgressBarValue(-1);
  };

  if (!animated || !startupSplashReady) {
    finalizeClose();
    return;
  }

  targetWindow.webContents.executeJavaScript('window.__finishStartupSplash?.();', true)
    .catch(() => {})
    .finally(() => {
      setTimeout(finalizeClose, STARTUP_SPLASH_CLOSE_DELAY_MS);
    });
}

async function createStartupSplashWindow() {
  if (isSmokeTest) {
    return null;
  }

  closeStartupSplashWindow({ animated: false });
  startupSplashReady = false;
  startupSplashClosing = false;
  startupSplashState = { ...DEFAULT_STARTUP_SPLASH_STATE };

  const splashWindow = new BrowserWindow({
    width: 320,
    height: 320,
    show: false,
    frame: false,
    transparent: true,
    resizable: false,
    movable: true,
    minimizable: false,
    maximizable: false,
    fullscreenable: false,
    skipTaskbar: true,
    center: true,
    hasShadow: false,
    backgroundColor: '#00000000',
    paintWhenInitiallyHidden: true,
    alwaysOnTop: true,
    webPreferences: {
      contextIsolation: true,
      sandbox: true,
      backgroundThrottling: false
    }
  });

  startupSplashWindow = splashWindow;
  splashWindow.setMenu(null);
  installSystemNavigationHandlers(splashWindow.webContents);
  splashWindow.once('ready-to-show', () => {
    if (!isUsableWindow(splashWindow) || startupSplashWindow !== splashWindow) {
      return;
    }
    splashWindow.show();
  });
  splashWindow.webContents.once('did-finish-load', () => {
    if (startupSplashWindow !== splashWindow) {
      return;
    }
    startupSplashReady = true;
    syncStartupSplashWindow(true);
  });
  splashWindow.on('closed', () => {
    if (startupSplashWindow === splashWindow) {
      startupSplashWindow = null;
    }
    startupSplashReady = false;
    startupSplashClosing = false;
    setMainWindowProgressBarValue(-1);
  });

  await splashWindow.loadFile(STARTUP_SPLASH_ENTRY_PATH);
  return splashWindow;
}

function resetMainWindowAuthSurfaceTracking() {
  mainWindowAuthSurfaceVisible = false;
  mainWindowAuthSurfaceVisitedSso = false;
}

function updateMainWindowAuthSurfaceTrackingForReveal(reason = '') {
  if (/login_screen/i.test(String(reason || ''))) {
    mainWindowAuthSurfaceVisible = true;
    mainWindowAuthSurfaceVisitedSso = false;
    return;
  }
  mainWindowAuthTransitionActive = false;
  resetMainWindowAuthSurfaceTracking();
}

function prepareMainWindowForAuthTransitionSplash() {
  if (mainWindowRevealCloseTimer) {
    clearTimeout(mainWindowRevealCloseTimer);
    mainWindowRevealCloseTimer = 0;
  }
  if (mainWindowPostRevealProbeTimer) {
    clearTimeout(mainWindowPostRevealProbeTimer);
    mainWindowPostRevealProbeTimer = 0;
  }

  if (!isSmokeTest && mainWindow && !mainWindow.isDestroyed()) {
    try {
      mainWindow.setOpacity(0);
      if (mainWindow.isVisible()) {
        mainWindow.hide();
      }
    } catch {
      // ignore hide failures
    }
  }

  mainWindowShown = false;
  mainWindowAuthTransitionActive = true;
  scheduleMainWindowRevealFallback(STARTUP_GLOBAL_REVEAL_FALLBACK_MS);
}

async function showAuthTransitionStartupSplash(payload = {}, source = '') {
  if (!mainWindow || mainWindow.isDestroyed()) {
    return { ok: false, reason: 'no-main-window' };
  }

  resetMainWindowAuthSurfaceTracking();
  prepareMainWindowForAuthTransitionSplash();

  const nextState = normalizeStartupSplashState({
    percent: Object.prototype.hasOwnProperty.call(payload || {}, 'percent') ? payload.percent : 18,
    phase: trimText(payload?.phase || 'Загрузка YuChat', 120),
    detail: trimText(payload?.detail || 'Авторизация принята, готовим рабочее пространство', 220)
  }, {
    ...DEFAULT_STARTUP_SPLASH_STATE,
    percent: Math.max(18, Number(startupSplashState?.percent || 0) || 0)
  });

  if (authTransitionSplashInFlight) {
    setStartupSplashState(nextState);
    return authTransitionSplashInFlight;
  }

  authTransitionSplashInFlight = (async () => {
    if (!isSmokeTest) {
      try {
        await createStartupSplashWindow();
      } catch (error) {
        runtimeWarn('[YuChat] Failed to show auth transition splash:', {
          source: trimText(source || '', 80),
          error: toSerializableError(error)
        });
      }
    }

    setStartupSplashState(nextState);

    return { ok: true };
  })();

  try {
    return await authTransitionSplashInFlight;
  } finally {
    authTransitionSplashInFlight = null;
  }
}

function trackAuthSurfaceNavigation(targetUrl = '', source = '') {
  if (!mainWindowAuthSurfaceVisible) {
    return;
  }

  if (isYuchatSsoUrl(targetUrl)) {
    mainWindowAuthSurfaceVisitedSso = true;
    return;
  }

  if (!isYuchatAuthCallbackUrl(targetUrl)) {
    return;
  }

  void showAuthTransitionStartupSplash({
    percent: 18,
    phase: 'Загрузка YuChat',
    detail: 'Авторизация принята, готовим рабочее пространство'
  }, `auth-return:${source || 'navigation'}`);
}

function showMainWindow(reason = '') {
  if (!mainWindow || mainWindow.isDestroyed()) {
    return;
  }

  if (mainWindowRevealFallbackTimer) {
    clearTimeout(mainWindowRevealFallbackTimer);
    mainWindowRevealFallbackTimer = 0;
  }

  updateMainWindowAuthSurfaceTrackingForReveal(reason);

  if (mainWindowShown) {
    if (!mainWindow.isVisible()) {
      mainWindow.show();
      applyMessengerWindowOpacity(mainWindow);
    }
    closeStartupSplashWindow({ animated: true });
    return;
  }

  mainWindowShown = true;
  mainWindowRevealFallbackDeferrals = 0;
  if (!mainWindow.isVisible()) {
    if (normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER) {
      revealMessengerWindowNow(mainWindow, {
        animate: true,
        focus: false,
        sourceBounds: mainWindowNormalBounds || mainWindow.getBounds()
      });
    } else {
      try {
        if (mainWindowNormalIsMaximized === true && !mainWindow.isMaximized()) {
          mainWindow.maximize();
        }
      } catch {
        // ignore maximize failures
      }
      mainWindow.show();
      applyMessengerWindowOpacity(mainWindow);
    }
  }
  mainWindow.focus();
  if (mainWindowPostRevealProbeTimer) {
    clearTimeout(mainWindowPostRevealProbeTimer);
    mainWindowPostRevealProbeTimer = 0;
  }
  mainWindowPostRevealProbeTimer = setTimeout(async () => {
    mainWindowPostRevealProbeTimer = 0;
    if (!mainWindow || mainWindow.isDestroyed() || !mainWindow.webContents || mainWindow.webContents.isDestroyed()) {
      return;
    }
    const targetContents = mainWindow.webContents;
    const probeResult = await ensureMainWindowRenderableSurface(targetContents, 'post-reveal');
    if (probeResult.ok) {
      return;
    }
    runtimeWarn('[YuChat] Main renderer stayed visually empty after fallback. Showing recovery page.', {
      reason: String(reason || '').slice(0, 120),
      markersBefore: probeResult.markersBefore,
      markersAfter: probeResult.markersAfter,
      forced: probeResult.forced
    });
  }, 4500);
  mainWindowPostRevealProbeTimer.unref?.();
  if (mainWindowRevealCloseTimer) {
    clearTimeout(mainWindowRevealCloseTimer);
    mainWindowRevealCloseTimer = 0;
  }

  const settleDelayMs = /login_screen/i.test(String(reason || ''))
    ? 180
    : MAIN_WINDOW_REVEAL_SETTLE_DELAY_MS;

  mainWindowRevealCloseTimer = setTimeout(() => {
    mainWindowRevealCloseTimer = 0;
    closeStartupSplashWindow({ animated: true });
  }, Math.max(0, Number(settleDelayMs) || 0));
}

function scheduleMainWindowRevealFallback(timeoutMs = MAIN_WINDOW_REVEAL_TIMEOUT_MS) {
  if (!mainWindow || mainWindow.isDestroyed() || mainWindowShown) {
    return;
  }

  if (mainWindowRevealFallbackTimer) {
    clearTimeout(mainWindowRevealFallbackTimer);
  }

  mainWindowRevealFallbackTimer = setTimeout(async () => {
    mainWindowRevealFallbackTimer = 0;
    if (!mainWindow || mainWindow.isDestroyed() || mainWindowShown) {
      return;
    }
    const isProgressStallFallback = Math.max(0, Number(timeoutMs) || 0) <= STARTUP_PROGRESS_STALL_FALLBACK_MS;
    if (isProgressStallFallback && mainWindow.webContents && !mainWindow.webContents.isDestroyed()) {
      const targetContents = mainWindow.webContents;
      const markers = await inspectCustomPreloadMarkers(targetContents);
      const healthy = hasHealthyCustomPreloadMarkers(markers);
      if (!healthy && mainWindowRevealFallbackDeferrals < STARTUP_PROGRESS_STALL_MAX_DEFERRALS) {
        mainWindowRevealFallbackDeferrals += 1;
        setStartupSplashState({
          percent: 94,
          phase: 'Завершаем загрузку',
          detail: 'Ждём данные интерфейса, чтобы не показывать пустое окно'
        });
        scheduleMainWindowRevealFallback(STARTUP_PROGRESS_STALL_RETRY_MS);
        return;
      }
      if (!healthy || !hasRenderableBodySurface(markers)) {
        const probeResult = await ensureMainWindowRenderableSurface(targetContents, 'progress-stall');
        if (probeResult?.forced?.reason === 'heartbeat-grace') {
          setStartupSplashState({
            percent: 95,
            phase: 'Почти готово',
            detail: 'Preload уже активен, ждём финальную отрисовку интерфейса'
          });
          scheduleMainWindowRevealFallback(STARTUP_PROGRESS_STALL_RETRY_MS);
          return;
        }
        runtimeWarn('[YuChat] Startup progress stalled before UI was ready; probe result.', {
          markersBefore: probeResult.markersBefore,
          markersAfter: probeResult.markersAfter,
          forced: probeResult.forced,
          ok: probeResult.ok
        });
        if (!probeResult.ok) {
          return;
        }
      }
    } else if (mainWindow.webContents && !mainWindow.webContents.isDestroyed()) {
      const targetContents = mainWindow.webContents;
      const probeResult = await ensureMainWindowRenderableSurface(targetContents, 'global-timeout');
      if (probeResult?.forced?.reason === 'heartbeat-grace') {
        runtimeInfo('[YuChat] Global timeout probe deferred because preload heartbeat is still fresh.', {
          markers: probeResult.markersBefore,
          forced: probeResult.forced
        });
        setStartupSplashState({
          percent: 95,
          phase: 'Почти готово',
          detail: 'Preload активен, ждём готовность контента перед показом окна'
        });
        scheduleMainWindowRevealFallback(STARTUP_PROGRESS_STALL_RETRY_MS);
        return;
      }
      if (!probeResult.ok) {
        runtimeWarn('[YuChat] Global startup timeout reached with empty surface. Showing recovery page.', {
          markersBefore: probeResult.markersBefore,
          markersAfter: probeResult.markersAfter,
          forced: probeResult.forced
        });
        return;
      }
    }
    if (!mainWindow || mainWindow.isDestroyed() || mainWindowShown) {
      return;
    }
    setStartupSplashState({
      percent: 96,
      phase: 'Завершаем загрузку',
      detail: 'Держим основное окно скрытым, пока интерфейс не будет готов'
    });
    scheduleMainWindowRevealFallback(STARTUP_PROGRESS_STALL_RETRY_MS);
  }, Math.max(0, Number(timeoutMs) || 0));
}

function getBgBase64() {
  const imgPath = path.join(__dirname, 'assets', 'pattern.png');
  if (!fs.existsSync(imgPath)) {
    return '';
  }

  try {
    const file = fs.readFileSync(imgPath);
    return `data:image/png;base64,${file.toString('base64')}`;
  } catch {
    return '';
  }
}

function normalizeText(value) {
  return String(value || '').toLowerCase().replace(/\s+/g, ' ').trim();
}

function cleanNotificationText(value, maxLength = 220) {
  return String(value || '').replace(/\s+/g, ' ').trim().slice(0, Math.max(32, Number(maxLength) || 220));
}

function cleanNotificationMultiline(value, maxLength = 520) {
  return String(value || '')
    .split(/\r?\n+/)
    .map((line) => String(line || '').replace(/\s+/g, ' ').trim())
    .filter(Boolean)
    .join('\n')
    .trim()
    .slice(0, Math.max(220, Number(maxLength) || 520));
}

function buildNotificationActivationPayload(payload = {}) {
  const workspaceId = typeof payload?.workspaceId === 'string'
    ? payload.workspaceId.trim()
    : '';
  const chatId = normalizeChatId(payload?.chatId || '');
  const normalizedThreadChatId = normalizeChatId(payload?.threadChatId || '');
  const threadChatId = /^t:/i.test(normalizedThreadChatId) ? normalizedThreadChatId : '';
  const messageId = typeof payload?.messageId === 'string'
    ? payload.messageId.trim()
    : '';
  const threadTitle = cleanNotificationText(payload?.threadTitle || '', 140);

  if (!workspaceId && !chatId && !threadChatId) {
    return null;
  }

  return {
    workspaceId,
    chatId,
    threadChatId,
    messageId,
    threadTitle
  };
}

function cleanReminderKey(value = '') {
  return String(value || '').trim().slice(0, 420);
}

function clearReminderNotificationTimer(reminderKey = '') {
  const key = cleanReminderKey(reminderKey);
  if (!key) return false;
  const existing = reminderNotificationTimers.get(key) || null;
  if (existing?.timer) {
    clearTimeout(existing.timer);
  }
  reminderNotificationTimers.delete(key);
  return true;
}

function clearAllReminderNotificationTimers() {
  reminderNotificationTimers.forEach((record) => {
    if (record?.timer) {
      clearTimeout(record.timer);
    }
  });
  reminderNotificationTimers.clear();
}

function closeActiveNotifications() {
  activeNotifications.forEach((notification) => {
    try {
      notification.close();
    } catch {
      // ignore notification close failures during shutdown
    }
  });
  activeNotifications.clear();
  recentNotificationKeys.clear();
}

function closeAuxiliaryWindows() {
  let windows = [];
  try {
    windows = BrowserWindow.getAllWindows();
  } catch {
    windows = [];
  }

  windows.forEach((windowRef) => {
    if (!windowRef || windowRef.isDestroyed() || windowRef === mainWindow) {
      return;
    }
    try {
      windowRef.__yuAllowClose = true;
      windowRef.destroy();
    } catch {
      // ignore auxiliary window teardown failures during shutdown
    }
  });
  owaWindowsByOrigin.clear();
}

function clearAppQuitFallbackTimer() {
  if (appQuitFallbackTimer) {
    clearTimeout(appQuitFallbackTimer);
    appQuitFallbackTimer = 0;
  }
}

function scheduleForcedAppExit(timeoutMs = SESSION_FLUSH_ON_QUIT_TIMEOUT_MS) {
  clearAppQuitFallbackTimer();
  const normalizedTimeoutMs = Math.max(0, Number(timeoutMs) || 0);
  if (!normalizedTimeoutMs) {
    return;
  }

  appQuitFallbackTimer = setTimeout(() => {
    appQuitFallbackTimer = 0;
    flushDiagnosticsArtifacts({ includePending: true });
    closeActiveNotifications();
    app.exit(0);
  }, normalizedTimeoutMs);
  appQuitFallbackTimer.unref?.();
}

function prepareRuntimeForAppQuit() {
  flushDiagnosticsArtifacts({ includePending: true });
  clearAllReminderNotificationTimers();
  closeActiveNotifications();
  closeStartupSplashWindow({ animated: false });
  closeAuxiliaryWindows();
  clearMessengerWindowHideTimer();

  if (mainWindowStatePersistTimer) {
    clearTimeout(mainWindowStatePersistTimer);
    mainWindowStatePersistTimer = 0;
  }
  if (mainWindowPostRevealProbeTimer) {
    clearTimeout(mainWindowPostRevealProbeTimer);
    mainWindowPostRevealProbeTimer = 0;
  }
  if (diagnosticFlushTimer) {
    clearTimeout(diagnosticFlushTimer);
    diagnosticFlushTimer = 0;
  }
  if (yuchatSessionFlushTimer) {
    clearTimeout(yuchatSessionFlushTimer);
    yuchatSessionFlushTimer = 0;
  }
  if (mainWindowRevealFallbackTimer) {
    clearTimeout(mainWindowRevealFallbackTimer);
    mainWindowRevealFallbackTimer = 0;
  }
  if (mainWindowRevealCloseTimer) {
    clearTimeout(mainWindowRevealCloseTimer);
    mainWindowRevealCloseTimer = 0;
  }
  if (smokeTimeoutHandle) {
    clearTimeout(smokeTimeoutHandle);
    smokeTimeoutHandle = 0;
  }
}

function scheduleReminderNotification(payload = {}) {
  const reminderKey = cleanReminderKey(payload?.reminderKey || payload?.key || '');
  if (!reminderKey) return false;

  const dueAt = Math.max(0, Number(payload?.dueAt || 0));
  const notificationSource = isPlainRecord(payload?.notification)
    ? payload.notification
    : payload;
  const notificationPayload = {
    title: cleanNotificationText(notificationSource?.title || 'Напоминание', 120) || 'Напоминание',
    subtitle: cleanNotificationText(notificationSource?.subtitle || '', 140),
    body: cleanNotificationText(notificationSource?.body || 'Пора вернуться к сообщению', 260) || 'Пора вернуться к сообщению',
    iconDataUrl: String(notificationSource?.iconDataUrl || '').trim()
  };

  clearReminderNotificationTimer(reminderKey);
  if (!dueAt) return false;

  const fireReminder = () => {
    clearReminderNotificationTimer(reminderKey);
    showAppNotification(notificationPayload);
  };

  const scheduleTick = () => {
    const record = reminderNotificationTimers.get(reminderKey) || null;
    if (!record) return;
    const remainingMs = Math.max(0, Number(record.dueAt || 0) - Date.now());
    if (remainingMs <= 200) {
      fireReminder();
      return;
    }
    const nextDelay = Math.max(200, Math.min(MAX_REMINDER_TIMER_DELAY_MS, remainingMs));
    const timer = setTimeout(scheduleTick, nextDelay);
    timer.unref?.();
    reminderNotificationTimers.set(reminderKey, {
      ...record,
      timer
    });
  };

  reminderNotificationTimers.set(reminderKey, {
    dueAt,
    notification: notificationPayload,
    timer: null
  });
  scheduleTick();
  return true;
}

function escapeSvgText(value) {
  return String(value || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function escapeSvgAttribute(value = '') {
  return String(value || '')
    .replace(/&/g, '&amp;')
    .replace(/"/g, '&quot;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

function getAuthorInitials(value) {
  const parts = cleanNotificationText(value, 80)
    .split(/\s+/)
    .filter(Boolean)
    .slice(0, 2);
  if (!parts.length) return 'U';
  return parts
    .map((part) => Array.from(part)[0] || '')
    .join('')
    .toUpperCase()
    .slice(0, 2) || 'U';
}

function buildGeneratedNotificationAvatarDataUrl(label = '') {
  const initials = escapeSvgText(getAuthorInitials(label));
  const svg = `
    <svg xmlns="http://www.w3.org/2000/svg" width="128" height="128" viewBox="0 0 128 128">
      <defs>
        <linearGradient id="g" x1="0" y1="0" x2="1" y2="1">
          <stop offset="0%" stop-color="#7cc4ff"/>
          <stop offset="100%" stop-color="#4f7dff"/>
        </linearGradient>
      </defs>
      <rect width="128" height="128" rx="64" fill="url(#g)"/>
      <text x="64" y="79" text-anchor="middle" font-family="-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif" font-size="54" font-weight="700" fill="#ffffff">${initials}</text>
    </svg>
  `.replace(/\s{2,}/g, ' ').trim();
  return `data:image/svg+xml;base64,${Buffer.from(svg, 'utf8').toString('base64')}`;
}

function buildCircularNotificationAvatarDataUrl(sourceDataUrl = '', label = '') {
  const normalizedSource = typeof sourceDataUrl === 'string' ? sourceDataUrl.trim() : '';
  const fallbackSource = buildGeneratedNotificationAvatarDataUrl(label || 'YuChat');
  const imageSource = normalizedSource || fallbackSource;
  const svg = `
    <svg xmlns="http://www.w3.org/2000/svg" width="128" height="128" viewBox="0 0 128 128">
      <defs>
        <clipPath id="clip">
          <circle cx="64" cy="64" r="64"/>
        </clipPath>
      </defs>
      <rect width="128" height="128" rx="64" fill="#edf3fb"/>
      <image href="${escapeSvgAttribute(imageSource)}" x="0" y="0" width="128" height="128" preserveAspectRatio="xMidYMid slice" clip-path="url(#clip)"/>
    </svg>
  `.replace(/\s{2,}/g, ' ').trim();
  return `data:image/svg+xml;base64,${Buffer.from(svg, 'utf8').toString('base64')}`;
}

function createNotificationAvatarImage(source = null, label = '') {
  const fallbackLabel = cleanNotificationText(label || 'YuChat', 120) || 'YuChat';
  let sourceDataUrl = '';

  if (typeof source === 'string' && /^data:image\//i.test(source.trim())) {
    sourceDataUrl = source.trim();
  } else if (source && typeof source.isEmpty === 'function' && typeof source.toDataURL === 'function' && !source.isEmpty()) {
    try {
      sourceDataUrl = source.toDataURL();
    } catch {
      sourceDataUrl = '';
    }
  }

  try {
    const rounded = buildCircularNotificationAvatarDataUrl(sourceDataUrl, fallbackLabel);
    const image = nativeImage?.createFromDataURL ? nativeImage.createFromDataURL(rounded) : null;
    if (image && typeof image.isEmpty === 'function' && !image.isEmpty()) {
      return image;
    }
  } catch {
    // fall through to raw/generated fallback
  }

  if (source && typeof source.isEmpty === 'function' && !source.isEmpty()) {
    return source;
  }

  try {
    const generated = nativeImage?.createFromDataURL
      ? nativeImage.createFromDataURL(buildGeneratedNotificationAvatarDataUrl(fallbackLabel))
      : null;
    if (generated && typeof generated.isEmpty === 'function' && !generated.isEmpty()) {
      return generated;
    }
  } catch {
    // fallback below
  }

  return null;
}

function isSystemNotificationText(text) {
  const normalizedText = normalizeText(text);
  if (!normalizedText) return false;
  if (normalizedText === 'системное сообщение' || normalizedText === 'system message') {
    return true;
  }

  const patterns = [
    'удален(а) с канала',
    'удален с канала',
    'удалена с канала',
    'пригласил(а)',
    'пригласил в канал',
    'пригласила в канал',
    'присоединился(-ась) к этому каналу',
    'присоединился к этому каналу',
    'присоединилась к этому каналу',
    'сделал(а) канал приватным',
    'сделал канал приватным',
    'сделала канал приватным',
    'сделал(а) канал публичным',
    'сделал канал публичным',
    'сделала канал публичным',
    'покинул(а) канал',
    'покинул канал',
    'покинула канал',
    'добавил(а)',
    'добавил в канал',
    'добавила в канал'
  ];

  return patterns.some((pattern) => normalizedText.includes(pattern));
}

function textHasMentionToken(text = '') {
  const source = String(text || '');
  if (!source.trim()) return false;
  if (/\[@[^\]]+\]\(([^)]+)\)/u.test(source)) return true;
  return /(^|[\s([{"'`>])@[\p{L}\p{N}_.-]{2,}(?=$|[\s)\]}:;,.!?<])/u.test(source);
}

function getNotificationBodyFromMessage(message) {
  const parts = Array.isArray(message?.content) ? message.content : [];
  for (const part of parts) {
    const text =
      (typeof part?.markdown === 'string' && part.markdown.trim()) ||
      (typeof part?.text === 'string' && part.text.trim()) ||
      '';
    if (text) {
      return text.replace(/\s+/g, ' ').trim().slice(0, 180);
    }
  }
  return 'Новое сообщение';
}

function messageMentionsCurrentUserForNotification(message = null) {
  const selfMemberId = typeof currentUserMemberId === 'string' ? currentUserMemberId.trim() : '';
  const selfName = typeof currentUserName === 'string' ? currentUserName.trim() : '';
  if (!selfMemberId && !selfName) {
    return false;
  }

  const mentionSources = [
    message?.mentions,
    message?.mentionedMembers,
    message?.mentionedUsers,
    message?.mention,
    message?.metadata?.mentions,
    message?.message?.mentions,
    message?.chatMessage?.mentions
  ];
  for (const source of mentionSources) {
    if (!source) continue;
    const items = Array.isArray(source) ? source : [source];
    const hasDirectMention = items.some((item) => {
      if (!item || typeof item !== 'object') return false;
      const mentionedMemberId = String(
        item?.memberId ||
        item?.mentionedMemberId ||
        item?.id ||
        item?.profile?.memberId ||
        ''
      ).trim();
      return Boolean(mentionedMemberId && selfMemberId && normalizeText(mentionedMemberId) === normalizeText(selfMemberId));
    });
    if (hasDirectMention) {
      return true;
    }
  }

  const rawText = getNotificationBodyFromMessage(message);
  if (!rawText) {
    return false;
  }

  const markdownMentionPattern = /\[@([^\]]+)\]\(([^)]+)\)/gu;
  let mentionMatch = null;
  while ((mentionMatch = markdownMentionPattern.exec(rawText)) !== null) {
    const mentionTarget = String(mentionMatch?.[2] || '').trim();
    if (
      mentionTarget
      && selfMemberId
      && (
        normalizeText(mentionTarget) === normalizeText(selfMemberId)
        || normalizeText(mentionTarget).endsWith(`:${normalizeText(selfMemberId)}`)
        || normalizeText(mentionTarget).endsWith(`/${normalizeText(selfMemberId)}`)
      )
    ) {
      return true;
    }
  }

  const normalizedTextBody = normalizeText(rawText).replace(/ё/g, 'е');
  const normalizedSelfName = normalizeText(selfName).replace(/ё/g, 'е');
  if (normalizedSelfName && normalizedTextBody.includes(`@${normalizedSelfName}`)) {
    return true;
  }
  return false;
}

function getMessageAuthorName(message, fallbackSources = []) {
  const extraSources = Array.isArray(fallbackSources)
    ? fallbackSources
    : [fallbackSources];
  const sources = [message, ...extraSources].filter(Boolean);

  for (const source of sources) {
    const candidates = [
      source?.memberName,
      source?.createdByName,
      source?.senderName,
      source?.authorName,
      source?.sender?.displayName,
      source?.sender?.fullName,
      source?.sender?.name,
      source?.sender?.profile?.fullName,
      source?.author?.displayName,
      source?.author?.fullName,
      source?.author?.name,
      source?.author?.profile?.fullName,
      source?.createdBy?.displayName,
      source?.createdBy?.fullName,
      source?.createdBy?.name,
      source?.createdBy?.profile?.fullName,
      source?.user?.displayName,
      source?.user?.fullName,
      source?.user?.name,
      source?.user?.profile?.fullName,
      source?.member?.displayName,
      source?.member?.fullName,
      source?.member?.name,
      source?.member?.profile?.fullName,
      source?.fullName,
      source?.displayName
    ];

    for (const candidate of candidates) {
      if (typeof candidate === 'string' && candidate.trim()) {
        return candidate.trim();
      }
    }
  }

  for (const source of sources) {
    const nestedCandidates = [
      findNestedRealtimeValue(source, 'authorName', { maxDepth: 8, maxNodes: 520 }),
      findNestedRealtimeValue(source, 'senderName', { maxDepth: 8, maxNodes: 520 }),
      findNestedRealtimeValue(source, 'memberName', { maxDepth: 8, maxNodes: 520 }),
      findNestedRealtimeValue(source, 'fullName', { maxDepth: 8, maxNodes: 520 }),
      findNestedRealtimeValue(source, 'displayName', { maxDepth: 8, maxNodes: 520 }),
      findNestedRealtimeValue(source, 'name', { maxDepth: 8, maxNodes: 520 })
    ];
    for (const candidate of nestedCandidates) {
      if (typeof candidate === 'string' && candidate.trim()) {
        return candidate.trim();
      }
    }
  }

  return '';
}

function getMessageAuthorAvatarUrl(message) {
  const candidates = [
    message?.sender?.avatar?.url,
    message?.sender?.avatarUrl,
    message?.sender?.profile?.avatar?.url,
    message?.sender?.profile?.primaryAvatar?.url,
    message?.author?.avatar?.url,
    message?.author?.avatarUrl,
    message?.author?.profile?.avatar?.url,
    message?.author?.profile?.primaryAvatar?.url,
    message?.createdBy?.avatar?.url,
    message?.createdBy?.avatarUrl,
    message?.createdBy?.profile?.avatar?.url,
    message?.createdBy?.profile?.primaryAvatar?.url,
    message?.user?.avatar?.url,
    message?.user?.avatarUrl,
    message?.user?.profile?.avatar?.url,
    message?.user?.profile?.primaryAvatar?.url,
    message?.member?.avatar?.url,
    message?.member?.avatarUrl,
    message?.member?.profile?.avatar?.url,
    message?.member?.profile?.primaryAvatar?.url,
    message?.avatar?.url,
    message?.avatarUrl
  ];

  for (const candidate of candidates) {
    if (typeof candidate === 'string' && candidate.trim()) {
      return candidate.trim();
    }
  }

  return '';
}

function getMessageAuthorMemberId(message) {
  const candidates = [
    message?.memberId,
    message?.authorMemberId,
    message?.senderMemberId,
    message?.fromMemberId,
    message?.createdByMemberId,
    message?.sender?.memberId,
    message?.author?.memberId,
    message?.createdBy?.memberId,
    message?.user?.memberId,
    message?.member?.memberId
  ];

  for (const candidate of candidates) {
    if (typeof candidate === 'string' && candidate.trim()) {
      return candidate.trim();
    }
  }

  return '';
}

function isOutgoingRealtimeMessage(message = null, event = null, payload = null) {
  if (!message || typeof message !== 'object') return false;
  const directOutgoingFlags = [
    message?.isMine,
    message?.isOutgoing,
    message?.outgoing,
    message?.fromMe,
    message?.mine,
    message?.myMessage,
    message?.ownMessage,
    message?.sender?.isMe,
    message?.author?.isMe,
    message?.createdBy?.isMe,
    message?.member?.isMe
  ];
  if (directOutgoingFlags.some((value) => value === true)) {
    return true;
  }

  const authorMemberId = getMessageAuthorMemberId(message);
  if (
    authorMemberId
    && currentUserMemberId
    && normalizeText(authorMemberId) === normalizeText(currentUserMemberId)
  ) {
    return true;
  }

  const nestedCandidates = [
    findNestedRealtimeValue(message, 'isOutgoing', { maxDepth: 6, maxNodes: 300 }),
    findNestedRealtimeValue(message, 'outgoing', { maxDepth: 6, maxNodes: 300 }),
    findNestedRealtimeValue(message, 'isMine', { maxDepth: 6, maxNodes: 300 }),
    findNestedRealtimeValue(message, 'fromMe', { maxDepth: 6, maxNodes: 300 }),
    findNestedRealtimeValue(event, 'isOutgoing', { maxDepth: 7, maxNodes: 360 }),
    findNestedRealtimeValue(payload, 'isOutgoing', { maxDepth: 8, maxNodes: 420 })
  ];
  return nestedCandidates.some((value) => value === true);
}

function getNotificationMeta(chatId, workspaceId) {
  const chatTitle = knownChatTitles.get(chatId) || '';
  const workspaceTitle = knownWorkspaceTitles.get(workspaceId) || '';

  if (chatTitle) {
    return {
      title: chatTitle,
      workspaceTitle,
      subtitle: workspaceTitle && normalizeText(workspaceTitle) !== normalizeText(chatTitle)
        ? workspaceTitle
        : ''
    };
  }

  return {
    title: workspaceTitle || 'YuChat',
    workspaceTitle,
    subtitle: ''
  };
}

function stripThreadDecorationFromNotificationTitle(value) {
  const text = cleanNotificationText(value || '', 160);
  if (!text) return '';
  return cleanNotificationText(
    text.replace(/\s*[•·]\s*ветка\s*:\s*.+$/i, ''),
    160
  );
}

function extractThreadTitleFromDecoratedNotificationTitle(value = '') {
  const text = cleanNotificationText(value || '', 200);
  if (!text) return '';
  const match = text.match(/[•·]\s*ветка\s*:\s*(.+)$/i);
  if (!match?.[1]) return '';
  return cleanNotificationText(match[1], 120);
}

function resolveRealtimeThreadParentChatId(payload = {}, event = null, message = null) {
  const candidates = [
    event?.parentChatId,
    event?.rootChatId,
    message?.thread?.parentChatId,
    message?.thread?.rootChatId,
    payload?.notification?.chatEvent?.newChatMessageSentEvent?.parentChatId,
    payload?.notification?.chatEvent?.newChatMessageSentEvent?.rootChatId,
    payload?.data?.notification?.chatEvent?.newChatMessageSentEvent?.parentChatId,
    payload?.data?.notification?.chatEvent?.newChatMessageSentEvent?.rootChatId,
    findNestedRealtimeValue(event, 'parentChatId', { maxDepth: 7, maxNodes: 380 }),
    findNestedRealtimeValue(event, 'rootChatId', { maxDepth: 7, maxNodes: 380 }),
    findNestedRealtimeValue(payload, 'parentChatId', { maxDepth: 8, maxNodes: 420 }),
    findNestedRealtimeValue(payload, 'rootChatId', { maxDepth: 8, maxNodes: 420 }),
    findNestedRealtimeValue(message, 'parentChatId', { maxDepth: 8, maxNodes: 420 }),
    findNestedRealtimeValue(message, 'rootChatId', { maxDepth: 8, maxNodes: 420 })
  ];
  for (const candidate of candidates) {
    const normalized = normalizeChatId(candidate || '');
    if (!normalized || /^t:/i.test(normalized)) continue;
    return normalized;
  }
  return '';
}

function resolveRealtimeThreadTitles(chatId = '', parentChatId = '', workspaceId = '', fallbackThreadTitle = '') {
  const threadChatId = normalizeChatId(chatId || '');
  const parentId = normalizeChatId(parentChatId || '');
  const parentMeta = getNotificationMeta(parentId || threadChatId, workspaceId);
  const channelTitle = cleanNotificationText(
    stripThreadDecorationFromNotificationTitle(parentMeta.title || '') || parentMeta.workspaceTitle || 'Канал',
    120
  ) || 'Канал';
  const rawThreadMetaTitle = cleanNotificationText(
    knownChatTitles.get(threadChatId)
    || fallbackThreadTitle
    || '',
    180
  );
  const threadTitleCandidate = cleanNotificationText(
    extractThreadTitleFromDecoratedNotificationTitle(rawThreadMetaTitle)
    || rawThreadMetaTitle
    || '',
    120
  );
  const threadTitle = (
    threadTitleCandidate
    && normalizeText(threadTitleCandidate) !== normalizeText(channelTitle)
    && !/^(t|thread):/i.test(threadTitleCandidate)
  ) ? threadTitleCandidate : '';

  return {
    channelTitle,
    threadTitle
  };
}

function resolveCachedNotificationAuthorName(chatId = '', fallbackName = '') {
  const explicitAuthorName = cleanNotificationText(fallbackName || '', 80);
  if (explicitAuthorName) return explicitAuthorName;
  return cleanNotificationText(knownChatAuthors.get(normalizeChatId(chatId || '')) || '', 80);
}

function buildStructuredNotificationFormat(options = {}) {
  const kind = String(options?.kind || '').trim();
  const authorName = cleanNotificationText(options?.authorName || '', 120) || 'Неизвестный';
  const messageBody = cleanNotificationText(options?.messageBody || '', 260) || 'Новое сообщение';
  const channelTitle = cleanNotificationText(options?.channelTitle || '', 120) || 'Канал';
  const threadTitle = cleanNotificationText(options?.threadTitle || '', 120) || 'Ветка';

  if (kind === 'direct') {
    return {
      title: cleanNotificationText(`Отправитель: ${authorName}`, 180) || 'Отправитель: Неизвестный',
      body: cleanNotificationMultiline(
        `Сообщение: ${messageBody}`,
        520
      ) || 'Сообщение: Новое сообщение'
    };
  }

  if (kind === 'thread') {
    return {
      title: cleanNotificationText(`Название канала: ${channelTitle}`, 200) || 'Название канала: Канал',
      body: cleanNotificationMultiline(
        [
          `Название ветки: ${threadTitle}`,
          `Отправитель: ${authorName}`,
          `Сообщение: ${messageBody}`
        ].join('\n'),
        520
      ) || 'Название ветки: Ветка\nОтправитель: Неизвестный\nСообщение: Новое сообщение'
    };
  }

  return {
    title: cleanNotificationText(`Название канала: ${channelTitle}`, 200) || 'Название канала: Канал',
    body: cleanNotificationMultiline(
      [
        `Отправитель: ${authorName}`,
        `Сообщение: ${messageBody}`
      ].join('\n'),
      520
    ) || 'Отправитель: Неизвестный\nСообщение: Новое сообщение'
  };
}

function buildRealtimeNotificationPayload(options = {}) {
  const chatId = normalizeChatId(options?.chatId || '');
  const threadChatId = normalizeChatId(options?.threadChatId || '');
  const isThreadMessage = options?.isThreadMessage === true;
  const isDirectConversation = options?.isDirectConversation === true || (!isThreadMessage && /^(p|u):/i.test(chatId));
  const authorName = resolveCachedNotificationAuthorName(chatId, options?.authorName || '');
  const snippet = cleanNotificationText(options?.body || '', 260) || 'Новое сообщение';
  const meta = getNotificationMeta(chatId, options?.workspaceId || '');
  const channelTitle = cleanNotificationText(
    options?.channelTitle
    || stripThreadDecorationFromNotificationTitle(meta.title || '')
    || meta.workspaceTitle
    || 'Канал',
    120
  ) || 'Канал';
  const threadTitle = cleanNotificationText(
    extractThreadTitleFromDecoratedNotificationTitle(options?.threadTitle || '')
    || options?.threadTitle
    || '',
    120
  );
  const authorAvatarUrl = cleanNotificationText(
    options?.authorAvatarUrl
    || options?.iconDataUrl
    || '',
    4096
  );
  const iconDataUrl = authorAvatarUrl || buildGeneratedNotificationAvatarDataUrl(authorName || channelTitle);
  const formatted = buildStructuredNotificationFormat({
    kind: isDirectConversation ? 'direct' : (isThreadMessage ? 'thread' : 'channel'),
    authorName,
    messageBody: snippet,
    channelTitle,
    threadTitle
  });

  return {
    title: cleanNotificationText(formatted.title || 'YuChat', 220) || 'YuChat',
    subtitle: '',
    body: cleanNotificationMultiline(formatted.body || '', 520) || 'Новое сообщение',
    iconDataUrl,
    authorName,
    workspaceId: String(options?.workspaceId || '').trim(),
    chatId,
    threadChatId: isThreadMessage && /^t:/i.test(threadChatId) ? threadChatId : '',
    messageId: String(options?.messageId || '').trim(),
    threadTitle
  };
}

function shouldSkipRealtimeNotification(chatId, title, body, options = {}) {
  if (isSystemNotificationText(body)) return true;
  if (options?.isOutgoing === true) return true;

  const authorMemberId = typeof options?.authorMemberId === 'string'
    ? options.authorMemberId.trim()
    : '';
  if (
    authorMemberId &&
    currentUserMemberId &&
    normalizeText(authorMemberId) === normalizeText(currentUserMemberId)
  ) {
    return true;
  }

  if (chatId && activeConversationChatId && chatIdsAreEquivalent(chatId, activeConversationChatId)) {
    return true;
  }

  const active = normalizeText(activeConversationTitle);
  const target = normalizeText(title);
  if (!active || !target) return false;

  return active === target || active.includes(target) || target.includes(active);
}

function tryParseRealtimeJsonObject(value) {
  if (!value) return null;
  if (typeof value === 'object') return value;
  if (typeof value !== 'string') return null;
  const raw = value.trim();
  if (!raw) return null;
  const normalized = /^\d+(?=[\[{])/.test(raw) ? raw.replace(/^\d+/, '') : raw;
  if (!normalized || !/^[\[{]/.test(normalized)) return null;
  try {
    const parsed = JSON.parse(normalized);
    return parsed && typeof parsed === 'object' ? parsed : null;
  } catch {
    return null;
  }
}

function findNestedRealtimeValue(source, propertyName, options = {}) {
  const targetName = String(propertyName || '').trim();
  if (!source || !targetName) return null;
  const maxDepth = Math.max(1, Number(options.maxDepth) || 6);
  const maxNodes = Math.max(20, Number(options.maxNodes) || 240);
  const queue = [{ value: source, depth: 0 }];
  const seen = new Set();
  let visited = 0;

  while (queue.length && visited < maxNodes) {
    const current = queue.shift();
    const value = current?.value;
    const depth = Number(current?.depth || 0);
    if (!value || typeof value !== 'object') continue;
    if (seen.has(value)) continue;
    seen.add(value);
    visited += 1;

    if (Object.prototype.hasOwnProperty.call(value, targetName)) {
      return value[targetName];
    }
    if (depth >= maxDepth) continue;

    if (Array.isArray(value)) {
      value.forEach((item) => {
        if (item && typeof item === 'object') {
          queue.push({ value: item, depth: depth + 1 });
        }
      });
      continue;
    }

    Object.keys(value).forEach((key) => {
      const next = value[key];
      if (next && typeof next === 'object') {
        queue.push({ value: next, depth: depth + 1 });
      }
    });
  }

  return null;
}

function collectRealtimePayloadObjects(rawPayload) {
  const collected = [];
  const enqueue = (value) => {
    if (!value) return;
    if (typeof value === 'string') {
      const parsed = tryParseRealtimeJsonObject(value);
      if (parsed) enqueue(parsed);
      return;
    }
    if (Array.isArray(value)) {
      value.forEach((item) => enqueue(item));
      return;
    }
    if (value && typeof value === 'object') {
      collected.push(value);
    }
  };

  enqueue(rawPayload);
  return collected;
}

function resolveRealtimeNotificationEvent(payload = {}) {
  const eventPayload =
    tryParseRealtimeJsonObject(payload?.notification?.chatEvent) ||
    tryParseRealtimeJsonObject(payload?.payload?.chatEvent) ||
    tryParseRealtimeJsonObject(payload?.data?.notification?.chatEvent) ||
    (payload?.notification?.chatEvent && typeof payload.notification.chatEvent === 'object' ? payload.notification.chatEvent : null) ||
    (payload?.payload?.chatEvent && typeof payload.payload.chatEvent === 'object' ? payload.payload.chatEvent : null) ||
    (payload?.data?.notification?.chatEvent && typeof payload.data.notification.chatEvent === 'object' ? payload.data.notification.chatEvent : null) ||
    (payload?.chatEvent && typeof payload.chatEvent === 'object' ? payload.chatEvent : null) ||
    payload;

  const candidates = [
    eventPayload?.newChatMessageSentEvent,
    eventPayload?.newMessageSentEvent,
    tryParseRealtimeJsonObject(eventPayload?.newChatMessageSentEvent),
    tryParseRealtimeJsonObject(eventPayload?.newMessageSentEvent),
    payload?.notification?.newChatMessageSentEvent,
    payload?.newChatMessageSentEvent,
    payload?.data?.notification?.chatEvent?.newChatMessageSentEvent
  ];
  for (const candidate of candidates) {
    const parsed = tryParseRealtimeJsonObject(candidate);
    if (parsed && typeof parsed === 'object') return parsed;
    if (candidate && typeof candidate === 'object') return candidate;
  }

  const nestedEvent =
    findNestedRealtimeValue(eventPayload, 'newChatMessageSentEvent', { maxDepth: 7, maxNodes: 360 }) ||
    findNestedRealtimeValue(payload, 'newChatMessageSentEvent', { maxDepth: 8, maxNodes: 420 });
  if (nestedEvent && typeof nestedEvent === 'object') return nestedEvent;
  return null;
}

function resolveRealtimeNotificationBadge(payload = {}, event = null) {
  const candidates = [
    event?.changedChatBadge,
    payload?.notification?.changedChatBadge,
    payload?.changedChatBadge,
    payload?.data?.notification?.chatEvent?.changedChatBadge
  ];
  for (const candidate of candidates) {
    const parsed = tryParseRealtimeJsonObject(candidate);
    if (parsed && typeof parsed === 'object') return parsed;
    if (candidate && typeof candidate === 'object') return candidate;
  }
  const nestedBadge =
    findNestedRealtimeValue(event, 'changedChatBadge', { maxDepth: 7, maxNodes: 360 }) ||
    findNestedRealtimeValue(payload, 'changedChatBadge', { maxDepth: 8, maxNodes: 420 });
  if (nestedBadge && typeof nestedBadge === 'object') return nestedBadge;
  return null;
}

function resolveRealtimeNotificationMessage(event = null) {
  if (!event || typeof event !== 'object') return null;
  const candidates = [
    event?.message,
    event?.payload?.message,
    tryParseRealtimeJsonObject(event?.message),
    tryParseRealtimeJsonObject(event?.payload?.message)
  ];
  for (const candidate of candidates) {
    if (candidate && typeof candidate === 'object' && !Array.isArray(candidate)) {
      return candidate;
    }
  }
  return null;
}

function resolveRealtimeNotificationChatId(event = null, badge = null, message = null) {
  const candidates = [
    event?.chatId,
    badge?.chatId,
    message?.chatId,
    message?.chat?.chatId,
    message?.chat?.id,
    message?.conversationId,
    message?.thread?.chatId
  ];
  for (const candidate of candidates) {
    const normalized = String(candidate || '').trim();
    if (normalized) return normalized;
  }
  const nestedCandidates = [
    findNestedRealtimeValue(event, 'chatId', { maxDepth: 7, maxNodes: 380 }),
    findNestedRealtimeValue(badge, 'chatId', { maxDepth: 7, maxNodes: 280 }),
    findNestedRealtimeValue(message, 'chatId', { maxDepth: 8, maxNodes: 420 }),
    findNestedRealtimeValue(event, 'conversationId', { maxDepth: 7, maxNodes: 380 }),
    findNestedRealtimeValue(message, 'conversationId', { maxDepth: 8, maxNodes: 420 })
  ];
  for (const candidate of nestedCandidates) {
    const normalized = String(candidate || '').trim();
    if (normalized) return normalized;
  }
  return '';
}

function resolveRealtimeNotificationWorkspaceId(event = null, badge = null, message = null) {
  const candidates = [
    badge?.workspaceId,
    event?.workspaceId,
    message?.workspaceId,
    message?.chat?.workspaceId,
    message?.chat?.workspace?.workspaceId,
    message?.chat?.workspace?.id
  ];
  for (const candidate of candidates) {
    const normalized = String(candidate || '').trim();
    if (normalized) return normalized;
  }
  const nestedCandidates = [
    findNestedRealtimeValue(badge, 'workspaceId', { maxDepth: 6, maxNodes: 260 }),
    findNestedRealtimeValue(event, 'workspaceId', { maxDepth: 7, maxNodes: 380 }),
    findNestedRealtimeValue(message, 'workspaceId', { maxDepth: 8, maxNodes: 420 })
  ];
  for (const candidate of nestedCandidates) {
    const normalized = String(candidate || '').trim();
    if (normalized) return normalized;
  }
  return '';
}

function handleRealtimeWsPayload(rawPayload) {
  const payloads = collectRealtimePayloadObjects(rawPayload);
  if (!payloads.length) return;

  for (const payload of payloads) {
    const event = resolveRealtimeNotificationEvent(payload);
    if (!event) continue;

    const message = resolveRealtimeNotificationMessage(event);
    if (!message || typeof message !== 'object') continue;

    const isOutgoing = isOutgoingRealtimeMessage(message, event, payload);
    if (isOutgoing) continue;

    const messageId = String(message?.messageId || '').trim();
    if (!messageId || seenRealtimeMessageIds.has(messageId)) continue;
    seenRealtimeMessageIds.add(messageId);

    if (message?.type && message.type !== 'USER_MESSAGE') continue;
    const authorName = getMessageAuthorName(message, [event, payload]);
    const authorMemberId = getMessageAuthorMemberId(message);
    if (
      authorMemberId &&
      currentUserMemberId &&
      normalizeText(authorMemberId) === normalizeText(currentUserMemberId)
    ) {
      continue;
    }
    if (authorName && currentUserName && normalizeText(authorName) === normalizeText(currentUserName)) {
      continue;
    }

    const badge = resolveRealtimeNotificationBadge(payload, event);
    const chatId = normalizeChatId(resolveRealtimeNotificationChatId(event, badge, message));
    const workspaceId = resolveRealtimeNotificationWorkspaceId(event, badge, message);
    const isThreadMessage = /^t:/i.test(chatId);
    const threadParentChatId = isThreadMessage
      ? resolveRealtimeThreadParentChatId(payload, event, message)
      : '';
    const notificationScopeChatId = isThreadMessage
      ? normalizeChatId(threadParentChatId || chatId)
      : chatId;
    const chatUnread = Number(
      badge?.chatUnread ||
      badge?.unreadCount ||
      badge?.badgeCount ||
      badge?.count ||
      badge?.chat?.chatUnread ||
      0
    ) || 0;
    const accountUnread = Number(badge?.accountUnread || 0) || 0;
    const hasUnreadSignal = Boolean(
      badge
      && (
        badge?.chatUnread != null
        || badge?.unreadCount != null
        || badge?.badgeCount != null
        || badge?.count != null
        || badge?.accountUnread != null
        || badge?.chat?.chatUnread != null
      )
    );

    if (hasUnreadSignal && chatUnread <= 0 && accountUnread <= 0) {
      continue;
    }

    const meta = getNotificationMeta(notificationScopeChatId, workspaceId);
    const rawBody = getNotificationBodyFromMessage(message);
    const explicitThreadTitle = isThreadMessage
      ? cleanNotificationText(
          event?.threadTitle
          || event?.threadName
          || event?.thread?.title
          || message?.threadTitle
          || message?.threadName
          || message?.thread?.title
          || findNestedRealtimeValue(event, 'threadTitle', { maxDepth: 7, maxNodes: 380 })
          || findNestedRealtimeValue(event, 'threadName', { maxDepth: 7, maxNodes: 380 })
          || findNestedRealtimeValue(message, 'threadTitle', { maxDepth: 8, maxNodes: 420 })
          || findNestedRealtimeValue(message, 'threadName', { maxDepth: 8, maxNodes: 420 })
          || findNestedRealtimeValue(payload, 'threadTitle', { maxDepth: 8, maxNodes: 420 })
          || findNestedRealtimeValue(payload, 'threadName', { maxDepth: 8, maxNodes: 420 })
          || '',
          120
        )
      : '';
    const threadTitles = isThreadMessage
      ? resolveRealtimeThreadTitles(chatId, threadParentChatId, workspaceId, explicitThreadTitle)
      : {
          channelTitle: cleanNotificationText(
            stripThreadDecorationFromNotificationTitle(meta.title || '') || meta.workspaceTitle || 'Канал',
            120
          ) || 'Канал',
          threadTitle: ''
        };
    const notificationPayload = buildRealtimeNotificationPayload({
      chatId: notificationScopeChatId,
      threadChatId: isThreadMessage ? chatId : '',
      workspaceId,
      authorName,
      body: rawBody,
      authorAvatarUrl: getMessageAuthorAvatarUrl(message),
      messageId,
      isThreadMessage,
      channelTitle: threadTitles.channelTitle,
      threadTitle: threadTitles.threadTitle
    });

    if (shouldSkipRealtimeNotification(notificationScopeChatId, meta.title, rawBody, {
      authorMemberId,
      isOutgoing,
      hasMention: textHasMentionToken(rawBody),
      mentionedMe: messageMentionsCurrentUserForNotification(message)
    })) continue;

    showAppNotification(notificationPayload);
    return;
  }
}

function attachRealtimeNotificationBridge(webContents) {
  if (!ENABLE_MAIN_WS_DEBUG_BRIDGE) {
    return;
  }
  const dbg = webContents.debugger;
  if (!(webContents.__yuChatRealtimeBridgeNetworkSessions instanceof Set)) {
    webContents.__yuChatRealtimeBridgeNetworkSessions = new Set();
  }

  webContents.__yuChatRealtimeBridgeEnableNetworkForSession = (sessionId = '') => {
    if (!dbg.isAttached()) return;
    const normalizedSessionId = typeof sessionId === 'string' ? sessionId.trim() : '';
    const sessionKey = normalizedSessionId || '__root__';
    if (webContents.__yuChatRealtimeBridgeNetworkSessions.has(sessionKey)) {
      return;
    }
    webContents.__yuChatRealtimeBridgeNetworkSessions.add(sessionKey);
    dbg.sendCommand('Network.enable', {}, normalizedSessionId || undefined).catch(() => {
      webContents.__yuChatRealtimeBridgeNetworkSessions.delete(sessionKey);
    });
  };

  if (!webContents.__yuChatRealtimeBridgeMessageHandlerBound) {
    webContents.__yuChatRealtimeBridgeMessageHandlerBound = true;
    dbg.on('message', (_event, method, params, sessionId) => {
      if (method === 'Target.attachedToTarget') {
        const attachedSessionId = typeof params?.sessionId === 'string'
          ? params.sessionId.trim()
          : '';
        if (attachedSessionId) {
          try {
            webContents.__yuChatRealtimeBridgeEnableNetworkForSession?.(attachedSessionId);
          } catch {
            // ignore target session bootstrap failures
          }
        }
        return;
      }

      if (method === 'Target.detachedFromTarget') {
        const detachedSessionId = typeof params?.sessionId === 'string'
          ? params.sessionId.trim()
          : '';
        if (detachedSessionId) {
          webContents.__yuChatRealtimeBridgeNetworkSessions.delete(detachedSessionId);
        }
        return;
      }

      if (method !== 'Network.webSocketFrameReceived') return;
      const rawPayload = params?.response?.payloadData || '';
      if (typeof rawPayload !== 'string' || !rawPayload) return;
      try {
        handleRealtimeWsPayload(rawPayload);
      } catch {
        // ignore main realtime notification parse failures
      }
      try {
        webContents.send('yuchat-realtime-ws-frame', rawPayload);
      } catch {
        // ignore renderer delivery failures
      }
    });
  }

  if (!webContents.__yuChatRealtimeBridgeDetachHandlerBound) {
    webContents.__yuChatRealtimeBridgeDetachHandlerBound = true;
    dbg.on('detach', () => {
      webContents.__yuChatRealtimeBridgeAttached = false;
      webContents.__yuChatRealtimeBridgeNetworkSessions.clear();
      if (webContents.isDestroyed()) return;
      setTimeout(() => {
        if (!webContents.isDestroyed()) {
          attachRealtimeNotificationBridge(webContents);
        }
      }, 1000);
    });
  }

  if (webContents.__yuChatRealtimeBridgeAttached) {
    return;
  }

  try {
    if (!dbg.isAttached()) {
      dbg.attach('1.3');
    }
  } catch (error) {
    runtimeWarn('[YuChat] Failed to attach realtime notification bridge:', error);
    return;
  }

  webContents.__yuChatRealtimeBridgeAttached = true;
  webContents.__yuChatRealtimeBridgeNetworkSessions.clear();
  webContents.__yuChatRealtimeBridgeEnableNetworkForSession('');
  dbg.sendCommand('Target.setAutoAttach', {
    autoAttach: true,
    waitForDebuggerOnStart: false,
    flatten: true
  }).catch(() => {});
}

function configureEmbeddedMessengerWebview(webPreferences = null, params = null) {
  if (!webPreferences || typeof webPreferences !== 'object') return false;
  let hostname = '';
  try {
    hostname = new URL(String(params?.src || '')).hostname.toLowerCase();
  } catch {
    hostname = '';
  }
  const partition = hostname === TELEGRAM_WEB_HOSTNAME
    ? TELEGRAM_WEB_PARTITION
    : (hostname === MAX_WEB_HOSTNAME ? MAX_WEB_PARTITION : '');
  if (!partition) return false;
  webPreferences.nodeIntegration = false;
  webPreferences.contextIsolation = true;
  webPreferences.sandbox = true;
  webPreferences.partition = partition;
  delete webPreferences.preload;
  return true;
}

async function createWindow() {
  appendSmokeLog('createWindow:start');
  configureYuchatSession();
  await createStartupSplashWindow().catch((error) => {
    runtimeWarn('[YuChat] Failed to create startup splash:', error);
  });
  mainWindowShown = false;
  resetMainWindowAuthSurfaceTracking();
  mainWindowAuthTransitionActive = false;
  mainWindowRevealFallbackDeferrals = 0;
  if (mainWindowRevealFallbackTimer) {
    clearTimeout(mainWindowRevealFallbackTimer);
    mainWindowRevealFallbackTimer = 0;
  }
  const savedWindowState = readMainWindowState();
  messengerWindowMode = WINDOW_MODE_NORMAL;
  messengerWindowShortcut = DEFAULT_MESSENGER_SHORTCUT;
  messengerWindowOpacity = DEFAULT_MESSENGER_OPACITY;
  messengerWindowAnimationDurationMs = DEFAULT_MESSENGER_ANIMATION_DURATION_MS;
  const shouldRestoreSavedNormalWindowBounds = shouldRestoreSavedMainWindowBounds(savedWindowState);
  mainWindowBoundsCustomized = savedWindowState?.boundsCustomized === true;
  mainWindowReadyForBoundsTracking = false;
  messengerWindowExpandedBounds = null;
  mainWindowNormalBounds = shouldRestoreSavedNormalWindowBounds
    ? (
      normalizePersistedWindowBounds(savedWindowState?.normalBounds, {
        minWidth: MAIN_WINDOW_MIN_WIDTH,
        minHeight: MAIN_WINDOW_MIN_HEIGHT
      }) || (
        Number.isFinite(savedWindowState?.x) && Number.isFinite(savedWindowState?.y)
          ? {
              x: Math.round(savedWindowState.x),
              y: Math.round(savedWindowState.y),
              width: Math.max(MAIN_WINDOW_MIN_WIDTH, Number(savedWindowState?.width) || MAIN_WINDOW_MIN_WIDTH),
              height: Math.max(MAIN_WINDOW_MIN_HEIGHT, Number(savedWindowState?.height) || MAIN_WINDOW_MIN_HEIGHT)
            }
          : null
      )
    )
    : null;
  mainWindowNormalIsMaximized = savedWindowState?.normalIsMaximized === true
    || savedWindowState?.isMaximized === true;
  const initialBounds = shouldRestoreSavedNormalWindowBounds
    ? {
        width: Math.max(MAIN_WINDOW_MIN_WIDTH, Number(savedWindowState?.width) || MAIN_WINDOW_MIN_WIDTH),
        height: Math.max(MAIN_WINDOW_MIN_HEIGHT, Number(savedWindowState?.height) || MAIN_WINDOW_MIN_HEIGHT),
        ...(Number.isFinite(savedWindowState?.x) && Number.isFinite(savedWindowState?.y)
          ? {
              x: Math.round(savedWindowState.x),
              y: Math.round(savedWindowState.y)
            }
          : null)
      }
    : {
        width: MAIN_WINDOW_MIN_WIDTH,
        height: MAIN_WINDOW_MIN_HEIGHT
      };

  mainWindow = new BrowserWindow({
    ...initialBounds,
    minWidth: MAIN_WINDOW_MIN_WIDTH,
    minHeight: MAIN_WINDOW_MIN_HEIGHT,
    resizable: true,
    maximizable: true,
    fullscreenable: true,
    show: false,
    backgroundColor: '#dfe5ec',
    paintWhenInitiallyHidden: true,
    webPreferences: {
      // fullCustomPreload.js incrementally composes local domain modules via relative require().
      // In Electron 41 sandboxed preload cannot load these filesystem modules reliably.
      // Keep sandbox disabled for full preload, but enable it for local-shell + thin preload path.
      sandbox: WINDOW_SANDBOX_ENABLED,
      contextIsolation: true,
      webviewTag: true,
      preload: WINDOW_PRELOAD_PATH,
      partition: YUCHAT_SESSION_PARTITION
    }
  });
  mainWindow.webContents.on('will-attach-webview', (event, webPreferences, params) => {
    if (!configureEmbeddedMessengerWebview(webPreferences, params)) {
      event.preventDefault();
    }
  });
  const mainWindowWebContentsId = Number(mainWindow?.webContents?.id || 0) || 0;
  applyMainWindowMinimumSize(mainWindow, {
    messengerMode: false
  });
  applyMessengerWindowOpacity(mainWindow);
  refreshMessengerWindowShortcutRegistration();
  setStartupSplashState({
    percent: 16,
    phase: 'Подготавливаем окно',
    detail: 'Запускаем оболочку приложения и привязываем безопасную сессию'
  });

  mainWindow.on('resize', () => {
    if (mainWindowReadyForBoundsTracking) {
      mainWindowBoundsCustomized = true;
    }
    persistMainWindowState(mainWindow);
  });
  mainWindow.on('move', () => {
    if (mainWindowReadyForBoundsTracking) {
      mainWindowBoundsCustomized = true;
    }
    persistMainWindowState(mainWindow);
  });
  mainWindow.on('close', () => {
    persistMainWindowState(mainWindow, { force: true });
    scheduleYuchatSessionFlush(0);
  });
  mainWindow.once('ready-to-show', () => {
    mainWindowReadyForBoundsTracking = true;
    if (smokeTestState) {
      recordSmokeEvent('window-ready-to-show');
    }
    scheduleMainWindowRevealFallback();
  });

  if ((ENABLE_DEVTOOLS_AUTO_OPEN || ENABLE_DIAGNOSTICS_CAPTURE) && !isSmokeTest) {
    mainWindow.webContents.once('dom-ready', () => {
      if (!mainWindow || mainWindow.isDestroyed()) return;
      if (mainWindow.webContents.isDevToolsOpened()) return;
      try {
        mainWindow.webContents.openDevTools({ mode: 'detach', activate: true });
      } catch (error) {
        runtimeWarn('[YuChat] Failed to auto-open DevTools:', error);
      }
    });
  }

  installDiagnosticsForWebContents(mainWindow.webContents);

  if (smokeTestState) {
    recordSmokeEvent('window-created', {
      bounds: mainWindow.getBounds()
    });
    smokeTestState.view.created = true;
    recordSmokeEvent('web-content-created');
  }

  mainWindow.webContents.setUserAgent(CUSTOM_YUCHAT_USER_AGENT);
  ensureSessionPreloadRegistration(mainWindow.webContents.session, WINDOW_PRELOAD_PATH, {
    source: 'createWindow:webContents'
  });
  await restorePersistedYuchatSessionCookies(mainWindow.webContents.session).catch(() => {});
  setStartupSplashState({
    percent: 28,
    phase: 'Восстанавливаем сессию',
    detail: 'Поднимаем сохранённый профиль и настройки доступа'
  });

  if (smokeTestState) {
    mainWindow.webContents.on('did-finish-load', () => {
      smokeTestState.shell.loaded = true;
      recordSmokeEvent('shell-did-finish-load', {
        url: mainWindow.webContents.getURL()
      });
      scheduleSmokeEvaluation('shell-did-finish-load', 250);
    });

    mainWindow.webContents.on('render-process-gone', (_event, details) => {
      addSmokeFailure('Shell render process exited unexpectedly.', details);
      void finalizeSmokeTest(false, 'Smoke test failed because the shell renderer crashed.');
    });

    smokeTimeoutHandle = setTimeout(() => {
      addSmokeFailure(`Smoke test timed out after ${SMOKE_TEST_TIMEOUT_MS}ms.`);
      void finalizeSmokeTest(false, 'Smoke test timed out before the app finished loading.');
    }, SMOKE_TEST_TIMEOUT_MS);
  }

  const initialLoad = LOCAL_SHELL_REQUESTED
    ? mainWindow.loadFile(LOCAL_SHELL_ENTRY_PATH)
    : mainWindow.webContents.loadURL(YUCHAT_ENTRY_URL);
  // Global guard: if renderer readiness signals never arrive, do not keep splash forever.
  scheduleMainWindowRevealFallback(STARTUP_GLOBAL_REVEAL_FALLBACK_MS);

  void initialLoad.catch((error) => {
    addSmokeFailure('Initial content navigation was rejected.', {
      error: toSerializableError(error)
    });
    void finalizeSmokeTest(false, 'Smoke test failed because the main content could not start navigation.');
  });
  appendSmokeLog(
    LOCAL_SHELL_REQUESTED
      ? `createWindow:loadFile-dispatched ${LOCAL_SHELL_ENTRY_PATH}`
      : `createWindow:loadURL-dispatched ${YUCHAT_ENTRY_URL}`
  );
  setStartupSplashState({
    percent: 36,
    phase: 'Подключаем YuChat',
    detail: 'Открываем рабочее пространство и запускаем первичную загрузку'
  });
  attachRealtimeNotificationBridge(mainWindow.webContents);
  installSystemNavigationHandlers(mainWindow.webContents);

  const scheduleSessionFlush = () => {
    scheduleYuchatSessionFlush(220);
  };
  mainWindow.webContents.on('did-finish-load', scheduleSessionFlush);
  mainWindow.webContents.on('will-navigate', (_event, url) => {
    trackAuthSurfaceNavigation(url, 'will-navigate');
  });
  mainWindow.webContents.on('will-frame-navigate', (_event, url, isInPlace, isMainFrame) => {
    if (isMainFrame) {
      trackAuthSurfaceNavigation(url, 'will-frame-navigate');
    }
  });
  mainWindow.webContents.on('will-redirect-navigation', (_event, url, isInPlace, isMainFrame) => {
    if (isMainFrame) {
      trackAuthSurfaceNavigation(url, 'will-redirect-navigation');
    }
  });
  mainWindow.webContents.on('did-start-loading', () => {
    const loadingUrl = mainWindow?.webContents?.getURL?.() || '';
    trackAuthSurfaceNavigation(loadingUrl, 'did-start-loading');
    setStartupSplashState({
      percent: 48,
      phase: 'Подключаем рабочее пространство',
      detail: 'Ждём ответ сервера и собираем стартовую страницу'
    });
    if (!smokeTestState) return;
    smokeTestState.view.didStartLoading = true;
    smokeTestState.view.currentUrl = loadingUrl;
    recordSmokeEvent('view-did-start-loading', {
      url: smokeTestState.view.currentUrl
    });
  });
  mainWindow.webContents.once('dom-ready', () => {
    setStartupSplashState({
      percent: 62,
      phase: 'Собираем интерфейс',
      detail: 'Страница готова, подключаем наш слой интерфейса поверх YuChat'
    });
    if (!isSmokeTest) {
      void recoverMissingCustomPreload(mainWindow.webContents, {
        source: 'mainWindow:dom-ready'
      });
    }
    if (!smokeTestState) return;
    smokeTestState.view.domReady = true;
    smokeTestState.view.currentUrl = mainWindow.webContents.getURL();
    recordSmokeEvent('view-dom-ready', {
      url: smokeTestState.view.currentUrl
    });
    scheduleSmokeEvaluation('view-dom-ready');
  });
  let rendererFallbackProbeTimer = setTimeout(async () => {
    rendererFallbackProbeTimer = 0;
    if (!mainWindow || mainWindow.isDestroyed() || !mainWindow.webContents || mainWindow.webContents.isDestroyed()) {
      return;
    }
    const targetContents = mainWindow.webContents;
    const markers = await inspectCustomPreloadMarkers(targetContents);
    if (hasHealthyCustomPreloadMarkers(markers)) {
      return;
    }
    const recentHeartbeat = getRecentPreloadHeartbeat(targetContents);
    if (recentHeartbeat && isPreloadHeartbeatReadyStage(recentHeartbeat.stage)) {
      runtimeInfo('[YuChat] Startup probe skipped forced fallback because preload heartbeat is fresh.', {
        markers,
        heartbeat: recentHeartbeat
      });
      return;
    }
    const forced = await forceRevealNativeSurfaceFallback(targetContents, 'startup-probe');
    runtimeWarn('[YuChat] Forced native fallback surface due to missing custom preload markers.', {
      markers,
      forced
    });
  }, 14_000);
  rendererFallbackProbeTimer.unref?.();
  mainWindow.on('closed', () => {
    if (rendererFallbackProbeTimer) {
      clearTimeout(rendererFallbackProbeTimer);
      rendererFallbackProbeTimer = 0;
    }
  });
  mainWindow.webContents.on('did-finish-load', scheduleSessionFlush);
  mainWindow.webContents.on('did-finish-load', () => {
    setStartupSplashState({
      percent: 74,
      phase: 'Применяем настройки',
      detail: 'Синхронизируем тему, состояние чатов и внутренние модули'
    });
    if (!smokeTestState) return;
    smokeTestState.view.didFinishLoad = true;
    smokeTestState.view.currentUrl = mainWindow.webContents.getURL();
    recordSmokeEvent('view-did-finish-load', {
      url: smokeTestState.view.currentUrl
    });
    scheduleSmokeEvaluation('view-did-finish-load');
  });
  mainWindow.webContents.on('did-stop-loading', scheduleSessionFlush);
  mainWindow.webContents.on('did-navigate', scheduleSessionFlush);
  mainWindow.webContents.on('did-navigate-in-page', (_event, url, isMainFrame) => {
    if (isMainFrame) {
      trackAuthSurfaceNavigation(url, 'did-navigate-in-page');
    }
    scheduleSessionFlush();
  });
  mainWindow.webContents.on('did-redirect-navigation', scheduleSessionFlush);
  mainWindow.webContents.on('did-fail-load', (event, errorCode, errorDescription, validatedURL, isMainFrame) => {
    if (isMainFrame) {
      setStartupSplashState({
        percent: 78,
        phase: 'Повторяем подключение',
        detail: trimText(errorDescription || 'YuChat ответил ошибкой, пробуем завершить загрузку', 160)
      });
    }

    if (
      isMainFrame
      && !LOCAL_SHELL_REQUESTED
      && !isSmokeTest
      && Number(errorCode || 0) !== -3
    ) {
      const failedUrl = trimText(validatedURL || '', 2200);
      const currentUrl = trimText(mainWindow?.webContents?.getURL?.() || '', 2200);
      const isDataPage = /^data:text\/html/i.test(failedUrl) || /^data:text\/html/i.test(currentUrl);
      if (!isDataPage) {
        runtimeWarn('[YuChat] Main page failed to load; showing recovery page.', {
          errorCode,
          errorDescription: trimText(errorDescription || '', 220),
          validatedURL: failedUrl || currentUrl || YUCHAT_ENTRY_URL
        });
        void revealMainWindowLoadFailurePage({
          errorCode,
          errorText: errorDescription || '',
          url: failedUrl || currentUrl || YUCHAT_ENTRY_URL
        });
      }
    }

    if (!smokeTestState || !isMainFrame) return;

    smokeTestState.view.lastFailLoad = {
      errorCode,
      errorDescription,
      validatedURL,
      isMainFrame
    };
    recordSmokeEvent('view-did-fail-load', {
      errorCode,
      errorDescription,
      validatedURL
    });
    scheduleSmokeEvaluation('view-did-fail-load', 200);
  });
  mainWindow.webContents.on('did-navigate', (_event, url) => {
    trackAuthSurfaceNavigation(url, 'did-navigate');
    if (!smokeTestState) return;
    smokeTestState.view.currentUrl = url;
    recordSmokeEvent('view-did-navigate', { url });
  });
  mainWindow.webContents.on('did-redirect-navigation', (_event, url, isInPlace, isMainFrame) => {
    if (isMainFrame) {
      trackAuthSurfaceNavigation(url, 'did-redirect-navigation');
    }
    if (!smokeTestState || !isMainFrame) return;
    smokeTestState.view.currentUrl = url;
    recordSmokeEvent('view-did-redirect-navigation', {
      url,
      isInPlace
    });
  });
  mainWindow.webContents.on('render-process-gone', (_event, details) => {
    if (!smokeTestState) return;
    addSmokeFailure('Embedded YuChat renderer exited unexpectedly.', details);
    void finalizeSmokeTest(false, 'Smoke test failed because the embedded renderer crashed.');
  });

  mainWindow.setMenu(null);

  mainWindow.on('closed', () => {
    try {
      if (mainWindowRevealFallbackTimer) {
        clearTimeout(mainWindowRevealFallbackTimer);
        mainWindowRevealFallbackTimer = 0;
      }
      if (mainWindowRevealCloseTimer) {
        clearTimeout(mainWindowRevealCloseTimer);
        mainWindowRevealCloseTimer = 0;
      }
      if (mainWindowPostRevealProbeTimer) {
        clearTimeout(mainWindowPostRevealProbeTimer);
        mainWindowPostRevealProbeTimer = 0;
      }
      closeStartupSplashWindow({ animated: false });
      mainWindowShown = false;
      if (smokeTestState && !smokeFinalizeInFlight) {
        addSmokeFailure('Main window closed before smoke test completed.');
        void finalizeSmokeTest(false, 'Smoke test failed because the window closed early.');
      }
      if (mainWindowWebContentsId > 0) {
        latestMainFrameStatusByWebContentsId.delete(mainWindowWebContentsId);
      }
    } catch (error) {
      const message = String(error?.message || error || '');
      if (!/object has been destroyed/i.test(message)) {
        runtimeWarn('[YuChat] Main window close handler failed:', error);
      }
    } finally {
      mainWindow = null;
      if (!isQuittingAfterSessionFlush) {
        closeAuxiliaryWindows();
        app.quit();
      }
    }
  });
}

app.on('select-client-certificate', (event, webContents, url, certificateList, callback) => {
  const targetUrl = String(url || '').trim();
  if (!isOwaRequestContext(targetUrl, webContents)) {
    return;
  }
  event.preventDefault();
  const owaWindow = findOwaWindowByWebContents(webContents);
  if (owaWindow) {
    scheduleOwaAutoReveal(owaWindow, normalizeOwaOrigin(targetUrl));
  }
  void selectOwaClientCertificate(targetUrl, certificateList, webContents)
    .then((certificate) => {
      callback(certificate || undefined);
      if (!certificate && owaWindow && owaWindow.__yuOwaBackgroundConnect === true) {
        revealOwaWindow(owaWindow);
      }
    })
    .catch(() => {
      callback();
    });
});

app.on('login', (event, webContents, details, authInfo, callback) => {
  const targetUrl = String(details?.url || '').trim();
  if (!isOwaRequestContext(targetUrl, webContents)) {
    return;
  }
  event.preventDefault();
  const owaWindow = findOwaWindowByWebContents(webContents);
  if (owaWindow) {
    scheduleOwaAutoReveal(owaWindow, normalizeOwaOrigin(targetUrl));
  }
  void promptOwaBasicAuthCredentials(details, authInfo, webContents)
    .then((credentials) => {
      if (credentials?.username) {
        callback(credentials.username, credentials.password || '');
        return;
      }
      callback();
      if (owaWindow && owaWindow.__yuOwaBackgroundConnect === true) {
        revealOwaWindow(owaWindow);
      }
    })
    .catch(() => {
      callback();
    });
});

if (!isSmokeTest && SHOULD_ENFORCE_SINGLE_INSTANCE) {
  app.on('second-instance', (_event, commandLine, workingDirectory) => {
    runtimeWarn('[YuChat] Prevented second instance launch.', {
      argvCount: Array.isArray(commandLine) ? commandLine.length : 0,
      workingDirectory: String(workingDirectory || '').trim()
    });
    if (!mainWindow || mainWindow.isDestroyed()) return;
    if (!mainWindowShown && focusStartupSplashWindow()) {
      return;
    }
    if (mainWindow.isMinimized()) {
      mainWindow.restore();
    }
    if (normalizeWindowMode(messengerWindowMode) === WINDOW_MODE_MESSENGER) {
      if (messengerWindowIsHidden === true || !mainWindow.isVisible()) {
        revealMessengerWindowNow(mainWindow, {
          animate: true,
          focus: false,
          sourceBounds: mainWindowNormalBounds || mainWindow.getBounds()
        });
      }
    } else if (!mainWindow.isVisible()) {
      mainWindow.show();
    }
    mainWindow.focus();
  });
}

if (hasSingleInstanceLock) {
  app.whenReady().then(async () => {
    await registerLocalAssetProtocol();
    createWindow();
  }).catch((error) => {
    if (!smokeTestState) {
      throw error;
    }

    addSmokeFailure('Electron failed during app startup.', {
      error: toSerializableError(error)
    });
    void finalizeSmokeTest(false, 'Smoke test failed before the app finished booting.');
  });

  app.on('web-contents-created', (_event, contents) => {
    try {
      configureYuchatSession(contents.session);
    } catch {
      // ignore auxiliary webContents session binding issues
    }
    installDiagnosticsForWebContents(contents);

    contents.on('will-attach-webview', (event, webPreferences, params) => {
      if (contents === mainWindow?.webContents && configureEmbeddedMessengerWebview(webPreferences, params)) {
        return;
      }
      event.preventDefault();
    });

    contents.setWindowOpenHandler?.(({ url = '' }) => {
      const normalizedUrl = String(url || '').trim();
      if (isSafeExternalUrl(normalizedUrl)) {
        void shell.openExternal(normalizedUrl);
      }
      return { action: 'deny' };
    });
  });
}

ipcMain.on('app-notification', (event, payload) => {
  showAppNotification(payload, {
    senderSession: event?.sender?.session || null,
    authToken: typeof payload?.authToken === 'string' ? payload.authToken : ''
  });
});

ipcMain.on('yuchat-notification-preferences', (_event, payload = {}) => {
  if (!isPlainRecord(payload)) return;
  systemNotificationPreferences = {
    yuchat: payload.yuchat !== false,
    telegram: payload.telegram !== false
  };
});

ipcMain.on('productivity-reminder-schedule', (_event, payload = {}) => {
  scheduleReminderNotification(payload);
});

ipcMain.on('productivity-reminder-cancel', (_event, payload = {}) => {
  clearReminderNotificationTimer(payload?.reminderKey || payload?.key || '');
});

ipcMain.on('chat-title-cache', (_event, payload = {}) => {
  const chatTitles = payload.chatTitles && typeof payload.chatTitles === 'object'
    ? payload.chatTitles
    : {};
  const chatAuthors = payload.chatAuthors && typeof payload.chatAuthors === 'object'
    ? payload.chatAuthors
    : {};
  const workspaceTitles = payload.workspaceTitles && typeof payload.workspaceTitles === 'object'
    ? payload.workspaceTitles
    : {};

  Object.entries(chatTitles).forEach(([chatId, title]) => {
    if (chatId && typeof title === 'string' && title.trim()) {
      knownChatTitles.set(chatId, title.trim());
    }
  });

  Object.entries(chatAuthors).forEach(([chatId, authorName]) => {
    if (chatId && typeof authorName === 'string' && authorName.trim()) {
      knownChatAuthors.set(chatId, authorName.trim());
    }
  });

  Object.entries(workspaceTitles).forEach(([workspaceId, title]) => {
    if (workspaceId && typeof title === 'string' && title.trim()) {
      knownWorkspaceTitles.set(workspaceId, title.trim());
    }
  });

  activeConversationTitle = typeof payload.activeConversationTitle === 'string'
    ? payload.activeConversationTitle.trim()
    : '';
  activeConversationChatId = typeof payload.activeConversationChatId === 'string'
    ? normalizeChatId(payload.activeConversationChatId.trim())
    : '';
  activeWorkspaceId = typeof payload.activeWorkspaceId === 'string'
    ? payload.activeWorkspaceId.trim()
    : '';
  currentUserName = typeof payload.myName === 'string'
    ? payload.myName.trim()
    : currentUserName;
  currentUserMemberId = typeof payload.myMemberId === 'string'
    ? payload.myMemberId.trim()
    : currentUserMemberId;
});

ipcMain.on('yuchat-startup-progress', (_event, payload = {}) => {
  setStartupSplashState({
    percent: payload?.percent,
    phase: payload?.phase,
    detail: payload?.detail
  });
  const reportedPercent = Math.max(0, Math.min(100, Math.round(Number(payload?.percent || 0) || 0)));
  if (reportedPercent >= 84 && reportedPercent < 100) {
    // If progress stops (for example around 92%), reveal the main window instead of infinite splash.
    scheduleMainWindowRevealFallback(STARTUP_PROGRESS_STALL_FALLBACK_MS);
  }
});

ipcMain.on('yuchat-preload-heartbeat', (event, payload = {}) => {
  recordPreloadHeartbeat(event, payload);
});

ipcMain.on('yuchat-ui-ready', (_event, payload = {}) => {
  const reason = trimText(payload?.reason || 'ready', 48).trim();
  if (reason === 'login_screen') {
    setStartupSplashState({
      percent: mainWindowAuthTransitionActive ? 72 : 100,
      phase: mainWindowAuthTransitionActive ? 'Завершаем вход' : 'Открываем вход',
      detail: mainWindowAuthTransitionActive
        ? 'SSO принято, ждём готовность кастомного интерфейса'
        : 'Сессия не найдена, показываем экран авторизации YuChat'
    });
    if (mainWindowAuthTransitionActive && trimText(payload?.authSurfaceKind || '', 64) !== 'sso_credentials') {
      scheduleMainWindowRevealFallback(STARTUP_GLOBAL_REVEAL_FALLBACK_MS);
      return;
    }
  } else {
    setStartupSplashState({
      percent: 100,
      phase: 'Готово',
      detail: 'Интерфейс YuChat полностью загружен'
    });
  }
  showMainWindow(reason ? `ui_ready:${reason}` : 'ui_ready');
  broadcastMessengerWindowShellState();
});

ipcMain.handle('yuchat-auth-loading-start', async (_event, payload = {}) => {
  const reason = trimText(payload?.reason || '', 96);
  if (/^(?:native-auth|preboot-auth)-/i.test(reason)) {
    return { ok: false, reason: 'ignored-early-auth-action' };
  }
  return showAuthTransitionStartupSplash(payload, 'renderer');
});

ipcMain.handle('yuchat-window-shell-get', () => getMessengerWindowShellState());

ipcMain.handle('yuchat-window-shell-set-shortcut', (_event, payload = {}) => {
  return {
    ok: false,
    reason: 'feature-disabled',
    state: getMessengerWindowShellState()
  };
});

ipcMain.handle('yuchat-window-shell-set-opacity', (_event, payload = {}) => {
  return {
    ok: false,
    reason: 'feature-disabled',
    state: getMessengerWindowShellState()
  };
});

ipcMain.handle('yuchat-window-shell-set-animation-duration', (_event, payload = {}) => {
  return {
    ok: false,
    reason: 'feature-disabled',
    state: getMessengerWindowShellState()
  };
});

ipcMain.handle('yuchat-window-shell-toggle-mode', () => ({
  ok: false,
  reason: 'feature-disabled',
  state: getMessengerWindowShellState()
}));

ipcMain.on('open-external-url', (_event, targetUrl = '') => {
  if (!isSafeExternalUrl(targetUrl)) return;
  shell.openExternal(targetUrl);
});

ipcMain.handle('yuchat-calendar-open-window', async (event, payload = {}) => {
  try {
    return await openOwaWindow(event, isPlainRecord(payload) ? payload : {});
  } catch (error) {
    return buildOwaErrorPayload(error, 'OWA_WINDOW_ERROR');
  }
});

ipcMain.handle('yuchat-calendar-fetch-events', async (event, payload = {}) => {
  try {
    return await fetchOwaCalendarEvents(event, isPlainRecord(payload) ? payload : {});
  } catch (error) {
    return buildOwaErrorPayload(error, 'OWA_CALENDAR_FETCH_ERROR');
  }
});

ipcMain.handle('yuchat-calendar-find-slots', async (event, payload = {}) => {
  try {
    return await findOwaMeetingSlots(event, isPlainRecord(payload) ? payload : {});
  } catch (error) {
    return buildOwaErrorPayload(error, 'OWA_AVAILABILITY_ERROR');
  }
});

ipcMain.handle('yuchat-telegram-state', async (_event, payload = {}) => {
  return getTelegramIntegrationState(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-connect', async (_event, payload = {}) => {
  return connectTelegramIntegration(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-send-code', async (_event, payload = {}) => {
  return sendTelegramCode(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-import-web-session', async (_event, payload = {}) => {
  return importTelegramWebSession(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-sign-in', async (_event, payload = {}) => {
  return signInTelegramIntegration(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-list-dialogs', async (_event, payload = {}) => {
  return listTelegramDialogs(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-list-messages', async (_event, payload = {}) => {
  return listTelegramMessages(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-list-participants', async (_event, payload = {}) => {
  return listTelegramParticipants(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-list-read-receipts', async (_event, payload = {}) => {
  return listTelegramMessageReadReceipts(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-resolve-username', async (_event, payload = {}) => {
  return resolveTelegramUsername(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-list-common-chats', async (_event, payload = {}) => {
  return listTelegramCommonChats(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-create-channel', async (_event, payload = {}) => {
  return createTelegramChannel(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-send-message', async (_event, payload = {}) => {
  return sendTelegramMessage(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-send-poll', async (_event, payload = {}) => {
  return sendTelegramPoll(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-vote-poll', async (_event, payload = {}) => {
  return voteTelegramPoll(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-edit-message', async (_event, payload = {}) => {
  return editTelegramMessage(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-toggle-reaction', async (_event, payload = {}) => {
  return toggleTelegramMessageReaction(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-pin-message', async (_event, payload = {}) => {
  return pinTelegramMessage(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-update-dialog-pin', async (_event, payload = {}) => {
  return updateTelegramDialogPinnedState(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-leave-dialog', async (_event, payload = {}) => {
  return leaveTelegramDialog(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-delete-messages', async (_event, payload = {}) => {
  return deleteTelegramMessages(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-send-files', async (_event, payload = {}) => {
  return sendTelegramFiles(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-forward-messages', async (_event, payload = {}) => {
  return forwardTelegramMessages(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-mark-read', async (_event, payload = {}) => {
  return markTelegramChatAsRead(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-update-archive-state', async (_event, payload = {}) => {
  return updateTelegramArchiveState(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-update-notify-settings', async (_event, payload = {}) => {
  return updateTelegramNotifySettings(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-start-call', async (_event, payload = {}) => {
  return startTelegramDirectCall(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-telegram-logout', async () => {
  return logoutTelegramIntegration();
});

ipcMain.handle('yuchat-telegram-open-window', async (_event, payload = {}) => {
  return {
    ok: false,
    code: 'TELEGRAM_WEB_DISABLED',
    error: 'Telegram Web отключён. Используйте Telegram API и MTProxy.',
    webMode: false
  };
});

ipcMain.handle('yuchat-trueconf-list-rooms', async (event, payload = {}) => {
  try {
    return await fetchTrueconfRooms(event, isPlainRecord(payload) ? payload : {});
  } catch (error) {
    return buildTrueconfErrorPayload(error, 'TRUECONF_LIST_ERROR');
  }
});

ipcMain.handle('yuchat-trueconf-room-deeplink', async (event, payload = {}) => {
  try {
    return await fetchTrueconfRoomDeeplink(event, isPlainRecord(payload) ? payload : {});
  } catch (error) {
    return buildTrueconfErrorPayload(error, 'TRUECONF_DEEPLINK_ERROR');
  }
});

ipcMain.handle('yuchat-trueconf-open-auth', async (event, payload = {}) => {
  return openTrueconfAuthorizationWindow(event, payload);
});

ipcMain.handle('yuchat-trueconf-chat-state', async (_event, payload = {}) => {
  return checkTrueconfChatConnection(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-trueconf-list-chats', async (_event, payload = {}) => {
  return listTrueconfChats(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-trueconf-list-messages', async (_event, payload = {}) => {
  return listTrueconfMessages(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-trueconf-send-message', async (_event, payload = {}) => {
  return sendTrueconfMessage(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-trueconf-logout', async (_event, payload = {}) => {
  return logoutTrueconfChatIntegration(isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-corporate-portal-fetch', async (event, payload = {}) => {
  return {
    ok: false,
    status: 0,
    url: '',
    text: '',
    error: 'CORPORATE_VACATION_DISABLED'
  };
});

ipcMain.handle('clipboard-write-text', (_event, text = '') => {
  clipboard.writeText(String(text || ''));
  return true;
});

ipcMain.handle('clipboard-read-text', () => clipboard.readText());

ipcMain.handle('save-export-file', async (_event, payload = {}) => {
  return saveExportFile(payload);
});

ipcMain.handle('save-export-archive', async (_event, payload = {}) => {
  return saveExportArchive(payload);
});

ipcMain.handle('open-import-file', async (_event, payload = {}) => {
  return openImportFile(payload);
});

ipcMain.handle('save-export-pdf', async (_event, payload = {}) => {
  return saveExportPdf(payload);
});

ipcMain.handle('yuchat-auth-state-get', (_event, payload = {}) => {
  const origin = getTrustedAuthStateOrigin(_event, payload);
  if (!origin) {
    return {};
  }
  const snapshot = getStoredAuthStateByOrigin(origin);
  runtimeWarn('[YuChat][auth-state] get', {
    origin,
    hasLocalStorage: Object.keys(snapshot?.localStorage || {}).length > 0,
    hasSessionStorage: Object.keys(snapshot?.sessionStorage || {}).length > 0
  });
  return snapshot;
});

ipcMain.handle('yuchat-auth-state-set', (_event, payload = {}) => {
  const origin = getTrustedAuthStateOrigin(_event, payload);
  if (!origin) {
    return false;
  }
  runtimeWarn('[YuChat][auth-state] set', {
    origin,
    clear: payload?.clear === true,
    replace: payload?.replace === true,
    pruneMissing: payload?.pruneMissing === true,
    localStorageKeys: Object.keys(payload?.localStorage || {}).length,
    sessionStorageKeys: Object.keys(payload?.sessionStorage || {}).length
  });
  const ok = setStoredAuthStateByOrigin(origin, payload);
  if (ok) {
    scheduleYuchatSessionFlush(0);
  }
  return ok;
});

ipcMain.handle('yuchat-session-backup-export', async (event, payload = {}) => {
  return exportYuchatSessionBackup(event, isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-session-backup-import', async (event, payload = {}) => {
  const optionsPayload = isPlainRecord(payload) ? payload : {};
  const snapshot = isPlainRecord(optionsPayload?.snapshot) ? optionsPayload.snapshot : payload;
  return importYuchatSessionBackup(snapshot, event, optionsPayload);
});

ipcMain.handle('media-access-status', (_event, mediaType = 'microphone') => {
  return getMediaAccessStatusSafe(String(mediaType || 'microphone').trim() || 'microphone');
});

ipcMain.handle('media-access-request', async (_event, mediaType = 'microphone') => {
  return requestMediaAccessSafe(String(mediaType || 'microphone').trim() || 'microphone');
});

ipcMain.handle('yuchat-prepare-vosk-dictation', async (event) => {
  return prepareVoskDictation(event);
});

ipcMain.handle('yuchat-transcribe-vosk-dictation', async (event, payload = {}) => {
  return transcribeVoskDictation(event, isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('open-attachment-via-os', async (event, payload = {}) => {
  return openAttachmentViaOs(event, payload);
});

ipcMain.handle('download-attachment-via-os', async (event, payload = {}) => {
  return downloadAttachmentViaOs(event, payload);
});

ipcMain.handle('abort-transfer-operation', async (_event, payload = {}) => {
  return abortTransferOperation(
    isPlainRecord(payload) ? payload?.transferId : '',
    isPlainRecord(payload) ? payload?.reason : 'canceled'
  );
});

ipcMain.handle('fetch-attachment-data-url', async (event, payload = {}) => {
  return fetchAttachmentDataUrl(event, payload);
});

ipcMain.handle('fetch-attachment-archive-file', async (event, payload = {}) => {
  return fetchAttachmentArchiveFile(event, payload);
});

ipcMain.handle('prepare-attachment-preview-url', async (event, payload = {}) => {
  return prepareAttachmentPreviewUrl(event, payload);
});

function normalizeLocalAssetRelativePath(relativePath = '') {
  return String(relativePath || '')
    .trim()
    .replace(/^\.?\//, '')
    .replace(/\\/g, '/');
}

function resolveLocalAssetPath(relativePath = '') {
  const normalizedRelativePath = normalizeLocalAssetRelativePath(relativePath);
  if (!normalizedRelativePath) {
    return '';
  }

  const assetPath = path.resolve(__dirname, normalizedRelativePath);
  const relativeFromBase = path.relative(__dirname, assetPath);
  if (!relativeFromBase || relativeFromBase.startsWith('..') || path.isAbsolute(relativeFromBase)) {
    return '';
  }

  if (!fs.existsSync(assetPath)) {
    return '';
  }

  return assetPath;
}

function resolveLocalAssetMimeType(assetPath = '') {
  const ext = path.extname(String(assetPath || '')).toLowerCase();
  if (ext === '.svg') return 'image/svg+xml';
  if (ext === '.png') return 'image/png';
  if (ext === '.jpg' || ext === '.jpeg') return 'image/jpeg';
  if (ext === '.gif') return 'image/gif';
  if (ext === '.webp') return 'image/webp';
  if (ext === '.mp4' || ext === '.m4v') return 'video/mp4';
  if (ext === '.mov') return 'video/quicktime';
  if (ext === '.webm') return 'video/webm';
  if (ext === '.mkv') return 'video/x-matroska';
  if (ext === '.avi') return 'video/x-msvideo';
  if (ext === '.mpv' || ext === '.mpg' || ext === '.mpeg' || ext === '.mpe' || ext === '.m2v') return 'video/mpeg';
  if (ext === '.ts' || ext === '.m2ts' || ext === '.mts') return 'video/mp2t';
  if (ext === '.3gp') return 'video/3gpp';
  if (ext === '.3g2') return 'video/3gpp2';
  if (ext === '.flv') return 'video/x-flv';
  if (ext === '.ogv') return 'video/ogg';
  if (ext === '.wmv') return 'video/x-ms-wmv';
  if (ext === '.asf') return 'video/x-ms-asf';
  if (ext === '.m4a') return 'audio/mp4';
  if (ext === '.aac') return 'audio/aac';
  if (ext === '.mp3') return 'audio/mpeg';
  if (ext === '.ogg' || ext === '.oga') return 'audio/ogg';
  if (ext === '.wav') return 'audio/wav';
  if (ext === '.gz' || ext === '.tgz') return 'application/gzip';
  if (ext === '.json') return 'application/json; charset=utf-8';
  return 'application/octet-stream';
}

function resolveLocalAssetRequestMimeType(requestUrl = null, assetPath = '') {
  const requestedMimeType = normalizeContentTypeToken(
    requestUrl?.searchParams?.get?.('contentType')
    || requestUrl?.searchParams?.get?.('type')
    || ''
  );
  if (/^(?:image|audio|video)\//i.test(requestedMimeType)) {
    return requestedMimeType;
  }
  return resolveLocalAssetMimeType(assetPath);
}

function buildLocalAssetUrl(relativePath = '') {
  const normalizedRelativePath = normalizeLocalAssetRelativePath(relativePath);
  if (!normalizedRelativePath) {
    return '';
  }
  const encodedPath = normalizedRelativePath
    .split('/')
    .filter(Boolean)
    .map((segment) => encodeURIComponent(segment))
    .join('/');
  return `${LOCAL_ASSET_PROTOCOL}://app/${encodedPath}`;
}

function buildProtocolFileResponse(filePath = '', options = {}) {
  const normalizedPath = String(filePath || '').trim();
  if (!normalizedPath || !fs.existsSync(normalizedPath)) {
    return new Response('Not found', {
      status: 404,
      headers: {
        'content-type': 'text/plain; charset=utf-8',
        'access-control-allow-origin': '*'
      }
    });
  }

  const mimeType = String(options?.contentType || '').trim() || resolveLocalAssetMimeType(normalizedPath);
  const cacheControl = String(options?.cacheControl || 'no-store').trim() || 'no-store';
  const baseHeaders = {
    'content-type': mimeType,
    'cache-control': cacheControl,
    'access-control-allow-origin': '*',
    'accept-ranges': 'bytes'
  };

  const stat = fs.statSync(normalizedPath);
  const totalSize = Math.max(0, Number(stat.size || 0));
  const rangeHeader = String(options?.range || '').trim();
  const rangeMatch = /^bytes=(\d*)-(\d*)$/i.exec(rangeHeader);
  if (rangeMatch && totalSize > 0) {
    const startCandidate = rangeMatch[1] ? Number(rangeMatch[1]) : 0;
    const endCandidate = rangeMatch[2] ? Number(rangeMatch[2]) : (totalSize - 1);
    const start = Math.max(0, Math.min(totalSize - 1, Number.isFinite(startCandidate) ? startCandidate : 0));
    const end = Math.max(start, Math.min(totalSize - 1, Number.isFinite(endCandidate) ? endCandidate : (totalSize - 1)));
    const chunkSize = Math.max(0, end - start + 1);
    const buffer = Buffer.alloc(chunkSize);
    const descriptor = fs.openSync(normalizedPath, 'r');
    try {
      fs.readSync(descriptor, buffer, 0, chunkSize, start);
    } finally {
      fs.closeSync(descriptor);
    }
    return new Response(buffer, {
      status: 206,
      headers: {
        ...baseHeaders,
        'content-length': String(chunkSize),
        'content-range': `bytes ${start}-${end}/${totalSize}`
      }
    });
  }

  return new Response(fs.readFileSync(normalizedPath), {
    status: 200,
    headers: {
      ...baseHeaders,
      'content-length': String(totalSize)
    }
  });
}

async function registerLocalAssetProtocol() {
  if (localAssetProtocolRegistered) {
    return;
  }

  await protocol.handle(LOCAL_ASSET_PROTOCOL, async (request) => {
    try {
      const requestUrl = new URL(String(request?.url || ''));
      if (String(requestUrl.host || '').trim().toLowerCase() === 'telegram') {
        const token = requestUrl.pathname
          .split('/')
          .filter(Boolean)
          .map((segment) => decodeURIComponent(segment))[0] || '';
        const record = telegramMediaTokenToRecord.get(String(token || '').trim()) || null;
        if (!record) {
          return new Response('Not found', {
            status: 404,
            headers: {
              'content-type': 'text/plain; charset=utf-8',
              'access-control-allow-origin': '*'
            }
          });
        }
        const filePath = await downloadTelegramMediaRecord(record);
        return buildProtocolFileResponse(filePath, {
          contentType: record.mimeType || resolveLocalAssetRequestMimeType(requestUrl, filePath),
          cacheControl: 'private, max-age=31536000',
          range: request.headers?.get?.('range') || ''
        });
      }

      if (String(requestUrl.host || '').trim().toLowerCase() === 'preview') {
        const token = requestUrl.pathname
          .split('/')
          .filter(Boolean)
          .map((segment) => decodeURIComponent(segment))[0] || '';
        const record = attachmentPreviewTokenToRecord.get(String(token || '').trim()) || null;
        if (!record?.filePath || !fs.existsSync(record.filePath)) {
          if (record?.token) {
            attachmentPreviewTokenToRecord.delete(record.token);
          }
          return new Response('Not found', {
            status: 404,
            headers: {
              'content-type': 'text/plain; charset=utf-8',
              'access-control-allow-origin': '*'
            }
          });
        }
        return buildProtocolFileResponse(record.filePath, {
          contentType: record.contentType || '',
          cacheControl: 'no-store',
          range: request.headers?.get?.('range') || ''
        });
      }

      if (String(requestUrl.host || '').trim().toLowerCase() === 'favorites') {
        const [fileId = '', fileName = 'attachment.bin'] = requestUrl.pathname
          .split('/')
          .filter(Boolean)
          .map((segment) => decodeURIComponent(segment));
        const filePath = resolveFavoritesFilePath(fileId, fileName);
        if (!filePath || !fs.existsSync(filePath)) {
          return new Response('Not found', {
            status: 404,
            headers: {
              'content-type': 'text/plain; charset=utf-8',
              'access-control-allow-origin': '*'
            }
          });
        }
        return buildProtocolFileResponse(filePath, {
          contentType: resolveLocalAssetRequestMimeType(requestUrl, filePath),
          cacheControl: 'private, max-age=31536000, immutable',
          range: request.headers?.get?.('range') || ''
        });
      }

      const relativePath = requestUrl.pathname
        .split('/')
        .filter(Boolean)
        .map((segment) => decodeURIComponent(segment))
        .join('/');
      const assetPath = resolveLocalAssetPath(relativePath);
      if (!assetPath) {
        return new Response('Not found', {
          status: 404,
          headers: {
            'content-type': 'text/plain; charset=utf-8',
            'access-control-allow-origin': '*'
          }
        });
      }

      return buildProtocolFileResponse(assetPath, {
        contentType: resolveLocalAssetRequestMimeType(requestUrl, assetPath),
        cacheControl: 'public, max-age=31536000, immutable',
        range: request.headers?.get?.('range') || ''
      });
    } catch (error) {
      runtimeWarn('[YuChat] Failed to serve local asset via protocol:', request?.url, error);
      return new Response('Internal error', {
        status: 500,
        headers: {
          'content-type': 'text/plain; charset=utf-8',
          'access-control-allow-origin': '*'
        }
      });
    }
  });

  localAssetProtocolRegistered = true;
}

ipcMain.handle('read-local-asset-data-url', (_event, relativePath = '') => {
  const normalizedRelativePath = normalizeLocalAssetRelativePath(relativePath);

  if (!normalizedRelativePath) {
    return '';
  }

  if (localAssetDataUrlCache.has(normalizedRelativePath)) {
    return localAssetDataUrlCache.get(normalizedRelativePath) || '';
  }

  const assetPath = resolveLocalAssetPath(normalizedRelativePath);
  if (!assetPath) {
    return '';
  }

  try {
    const file = fs.readFileSync(assetPath);
    const mimeType = resolveLocalAssetMimeType(assetPath);

    const dataUrl = `data:${mimeType};base64,${file.toString('base64')}`;
    localAssetDataUrlCache.set(normalizedRelativePath, dataUrl);
    return dataUrl;
  } catch (error) {
    runtimeWarn('[YuChat] Failed to read local asset:', assetPath, error);
    return '';
  }
});

ipcMain.handle('read-local-asset-url', (_event, relativePath = '') => {
  return buildLocalAssetUrl(relativePath);
});

ipcMain.handle('yuchat-favorites-store-file', async (event, payload = {}) => {
  return storeFavoritesFile(event, isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-favorites-prepare-playable-video', async (event, payload = {}) => {
  return prepareFavoritesPlayableVideo(event, isPlainRecord(payload) ? payload : {});
});

ipcMain.handle('yuchat-upload-presigned-file', async (_event, payload = {}) => {
  return uploadBinaryToExternalUrl(_event, payload);
});

ipcMain.handle('yuchat-get-display-media-source', async () => {
  const accessStatus = getScreenCaptureAccessStatus();
  if (process.platform === 'darwin' && accessStatus && accessStatus !== 'granted' && accessStatus !== 'unknown') {
    return {
      id: '',
      name: '',
      accessStatus
    };
  }

  try {
    const preferredSource = await getPreferredDesktopCaptureSource();
    return {
      id: String(preferredSource?.id || '').trim(),
      name: String(preferredSource?.name || '').trim(),
      accessStatus
    };
  } catch (error) {
    return {
      id: '',
      name: '',
      accessStatus,
      error: String(error?.message || error || 'unknown')
    };
  }
});

ipcMain.handle('capture-current-view', async () => {
  try {
    if (!mainWindow || mainWindow.webContents.isDestroyed()) {
      return '';
    }

    if (
      currentViewCaptureCache.dataUrl &&
      (Date.now() - Number(currentViewCaptureCache.capturedAt || 0)) < CAPTURE_CURRENT_VIEW_CACHE_TTL_MS
    ) {
      return currentViewCaptureCache.dataUrl;
    }

    if (!currentViewCapturePromise) {
      currentViewCapturePromise = (async () => {
        const image = await mainWindow.webContents.capturePage();
        if (image.isEmpty()) {
          currentViewCaptureCache = {
            dataUrl: '',
            capturedAt: 0
          };
          return '';
        }

        const dataUrl = image.toDataURL();
        currentViewCaptureCache = {
          dataUrl,
          capturedAt: Date.now()
        };
        return dataUrl;
      })().finally(() => {
        currentViewCapturePromise = null;
      });
    }

    return await currentViewCapturePromise;
  } catch (error) {
    runtimeWarn('[YuChat] Failed to capture current view:', error);
    return '';
  }
});

ipcMain.handle('yuchat-diagnostics-state', () => {
  if (!ENABLE_DIAGNOSTICS_CAPTURE || !diagnosticsState) {
    return {
      enabled: false
    };
  }
  flushDiagnosticsArtifacts({ includePending: true });
  return {
    enabled: true,
    startedAt: diagnosticsState.startedAt,
    flushCount: diagnosticsState.flushCount,
    consoleEntryCount: diagnosticConsoleEntries.length,
    networkEntryCount: diagnosticNetworkEntries.length,
    pendingRequestCount: diagnosticPendingRequestsById.size,
    artifacts: {
      summaryPath: diagnosticsSummaryPath,
      consolePath: diagnosticsConsolePath,
      harPath: diagnosticsHarPath,
      rawNetworkPath: diagnosticsRawNetworkPath
    }
  };
});

app.on('before-quit', (event) => {
  if (isQuittingAfterSessionFlush) {
    return;
  }

  event.preventDefault();
  isQuittingAfterSessionFlush = true;
  prepareRuntimeForAppQuit();
  // Session flush can occasionally stall inside Electron; force exit if it takes too long.
  scheduleForcedAppExit();
  void flushYuchatSessionStorage().finally(() => {
    flushDiagnosticsArtifacts({ includePending: true });
    app.quit();
  });
});

app.on('will-quit', () => {
  try {
    globalShortcut.unregisterAll();
  } catch {
    // ignore global shortcut cleanup failures
  }
  clearAppQuitFallbackTimer();
  flushDiagnosticsArtifacts({ includePending: true });
});

app.on('window-all-closed', () => {
  app.quit();
});
