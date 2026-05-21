const { contextBridge, ipcRenderer } = require('electron');

const bridge = Object.freeze({
  notify(payload) {
    ipcRenderer.send('app-notification', payload);
  },
  getEnvironment() {
    return Object.freeze({
      platform: process.platform,
      runtime: 'electron',
      shellVersion: '2026-04-24-r18-no-updater'
    });
  }
});

contextBridge.exposeInMainWorld('electronAPI', bridge);
contextBridge.exposeInMainWorld('desktopBridge', bridge);
