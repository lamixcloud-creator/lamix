const path = require('path');
let ipcRenderer = null;
try {
  ({ ipcRenderer } = require('electron'));
} catch {
  ipcRenderer = null;
}

const PREBOOT_STYLE_ID = 'yuchat-preboot-style';
const PREBOOT_ERROR_BANNER_ID = 'yuchat-preboot-error-banner';
const PREBOOT_FALLBACK_TIMER_MS = 18000;
const FULL_CUSTOM_PRELOAD_MODULE_PATH = path.join(__dirname, 'fullCustomPreload.js');
const WINDOW_ROLE_ARG_PREFIX = '--yu-window-role=';
const CUSTOM_PRELOAD_BYPASS_ROLES = new Set([
  'trueconf-auth'
]);
const PRELOAD_DIAGNOSTICS_ENABLED = (
  process.argv.includes('--capture-diagnostics')
  || process.env.YUCHAT_CAPTURE_DIAGNOSTICS === '1'
  || process.env.YUCHAT_ENABLE_RUNTIME_LOGS === '1'
);
const ENABLE_PREBOOT_ERROR_BANNERS = (
  process.argv.includes('--enable-preboot-error-banners')
  || process.env.YUCHAT_ENABLE_PREBOOT_ERROR_BANNERS === '1'
);
let nativeFallbackTimer = 0;
let fullCustomPreloadLoaded = false;

function clearNativeFallbackSurfaceTimer() {
  if (!nativeFallbackTimer) return;
  window.clearTimeout(nativeFallbackTimer);
  nativeFallbackTimer = 0;
}

function markBootstrapState(value = '1') {
  try {
    document.documentElement?.setAttribute('data-yu-bootstrap-preload', String(value || '1'));
  } catch {}
}

function logBootstrapTrace(eventName = '', payload = {}) {
  if (!PRELOAD_DIAGNOSTICS_ENABLED) return;
  try {
    console.info(`[YU_BOOTSTRAP] ${String(eventName || '').trim()}`, JSON.stringify(payload || {}));
  } catch {}
}

function sendPreloadHeartbeat(stage = '', payload = {}) {
  const safeStage = String(stage || '').trim();
  if (!safeStage || !ipcRenderer || typeof ipcRenderer.send !== 'function') return;
  try {
    ipcRenderer.send('yuchat-preload-heartbeat', {
      stage: safeStage,
      source: 'preloadBootstrap',
      ...(payload && typeof payload === 'object' ? payload : {})
    });
  } catch {}
}

function getWindowRoleFromArgv() {
  try {
    const args = Array.isArray(process.argv) ? process.argv : [];
    for (let index = args.length - 1; index >= 0; index -= 1) {
      const value = String(args[index] || '').trim();
      if (!value.startsWith(WINDOW_ROLE_ARG_PREFIX)) continue;
      return value.slice(WINDOW_ROLE_ARG_PREFIX.length).trim().toLowerCase();
    }
  } catch {}
  return '';
}

function ensurePrebootStyle() {
  if (document.getElementById(PREBOOT_STYLE_ID)) return;
  const style = document.createElement('style');
  style.id = PREBOOT_STYLE_ID;
  style.textContent = `
    html,
    body {
      background: #dfe5ec !important;
    }

    body.yc-native-profile-open #yuchat-full-custom-root,
    body.yc-native-profile-open .yc-top-status,
    body.yc-native-profile-open .yc-birthday-reminders,
    body.yc-native-profile-open .yc-transfer-progress {
      display: none !important;
    }

    body.yc-native-profile-open {
      background:
        radial-gradient(circle at 18% 24%, rgba(83, 178, 235, 0.12), transparent 34%),
        radial-gradient(circle at 82% 76%, rgba(255, 157, 85, 0.16), transparent 30%),
        linear-gradient(135deg, #f7fbff 0%, #ffffff 54%, #fff8ed 100%) !important;
    }

    body.yc-native-profile-open > :not(style#${PREBOOT_STYLE_ID}):not(script) {
      animation: ycNativeAuthSurfaceIn 420ms cubic-bezier(0.22, 1, 0.36, 1) both;
    }

    body.yc-native-profile-open :is(button, [role="button"], input, a) {
      transition:
        transform 180ms cubic-bezier(0.2, 0, 0, 1),
        box-shadow 180ms cubic-bezier(0.22, 1, 0.36, 1),
        border-color 180ms cubic-bezier(0.22, 1, 0.36, 1),
        background-color 180ms cubic-bezier(0.22, 1, 0.36, 1),
        opacity 180ms cubic-bezier(0.22, 1, 0.36, 1);
    }

    body.yc-native-profile-open :is(button, [role="button"], a):hover {
      transform: translateY(-1px);
    }

    body.yc-native-profile-open input:focus {
      outline: 2px solid rgba(76, 145, 199, 0.28) !important;
      outline-offset: 2px !important;
    }

    @keyframes ycNativeAuthSurfaceIn {
      0% {
        opacity: 0;
        transform: translateY(12px) scale(0.985);
        filter: blur(8px);
      }
      100% {
        opacity: 1;
        transform: translateY(0) scale(1);
        filter: blur(0);
      }
    }

    @media (prefers-reduced-motion: reduce) {
      body.yc-native-profile-open > :not(style#${PREBOOT_STYLE_ID}):not(script) {
        animation: none;
      }
    }
  `;
  (document.head || document.documentElement || document.body)?.appendChild(style);
}

function ensureFatalBanner(message = '') {
  if (!ENABLE_PREBOOT_ERROR_BANNERS) {
    const existingBanner = document.getElementById(PREBOOT_ERROR_BANNER_ID);
    if (existingBanner instanceof HTMLElement) {
      existingBanner.remove();
    }
    return;
  }
  const host = document.body || document.documentElement;
  if (!(host instanceof HTMLElement)) return;

  let banner = document.getElementById(PREBOOT_ERROR_BANNER_ID);
  if (!(banner instanceof HTMLElement)) {
    banner = document.createElement('div');
    banner.id = PREBOOT_ERROR_BANNER_ID;
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
    banner.style.whiteSpace = 'pre-wrap';
    banner.style.wordBreak = 'break-word';
    banner.style.pointerEvents = 'auto';
    host.appendChild(banner);
  }
  if (banner.dataset.prebootDismissBound !== '1') {
    banner.dataset.prebootDismissBound = '1';
    banner.addEventListener('click', (event) => {
      const target = event.target instanceof HTMLElement
        ? event.target.closest('[data-preboot-fatal-close]')
        : null;
      if (!(target instanceof HTMLElement)) return;
      event.preventDefault();
      event.stopPropagation();
      banner.remove();
    });
  }
  let messageNode = banner.querySelector('[data-preboot-fatal-message]');
  let closeButton = banner.querySelector('[data-preboot-fatal-close]');
  if (!(messageNode instanceof HTMLElement) || !(closeButton instanceof HTMLButtonElement)) {
    banner.innerHTML = '';
    const shell = document.createElement('div');
    shell.style.display = 'flex';
    shell.style.alignItems = 'flex-start';
    shell.style.gap = '12px';
    shell.style.minWidth = '0';

    messageNode = document.createElement('div');
    messageNode.dataset.prebootFatalMessage = '1';
    messageNode.style.flex = '1 1 auto';
    messageNode.style.minWidth = '0';
    messageNode.style.whiteSpace = 'pre-wrap';
    messageNode.style.wordBreak = 'break-word';

    closeButton = document.createElement('button');
    closeButton.type = 'button';
    closeButton.dataset.prebootFatalClose = '1';
    closeButton.setAttribute('aria-label', 'Скрыть ошибку');
    closeButton.setAttribute('title', 'Скрыть ошибку');
    closeButton.textContent = '×';
    closeButton.style.width = '26px';
    closeButton.style.height = '26px';
    closeButton.style.border = '0';
    closeButton.style.borderRadius = '999px';
    closeButton.style.background = 'rgba(255, 255, 255, 0.18)';
    closeButton.style.color = '#fff';
    closeButton.style.font = '600 18px/1 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
    closeButton.style.cursor = 'pointer';
    closeButton.style.flex = '0 0 auto';
    closeButton.style.padding = '0';

    shell.appendChild(messageNode);
    shell.appendChild(closeButton);
    banner.appendChild(shell);
  }
  messageNode.textContent = message;
}

function hasHealthyCustomShellMarkers() {
  try {
    const root = document.getElementById('yuchat-full-custom-root');
    if (!(root instanceof HTMLElement) || !root.isConnected) return false;
    if (root.childElementCount < 1) return false;
    const hasRenderableSize = Number(root.clientWidth || 0) > 24 || Number(root.clientHeight || 0) > 24;
    if (!hasRenderableSize) return false;
    const rootText = String(root.innerText || root.textContent || '')
      .replace(/\s+/g, ' ')
      .trim();
    if (rootText.length >= 20) return true;
    const interactiveNodes = root.querySelectorAll('input, button, a, form, [role="button"]');
    return interactiveNodes.length > 0;
  } catch {
    return false;
  }
}

function hasVisibleNativeSurfaceContent() {
  try {
    const body = document.body;
    if (!(body instanceof HTMLElement)) return false;
    const bodyText = String(body.innerText || body.textContent || '')
      .replace(/\s+/g, ' ')
      .trim();
    if (bodyText.length >= 20) return true;
    const interactiveNodes = document.querySelectorAll('input, button, a, form, [role="button"]');
    return interactiveNodes.length > 0;
  } catch {
    return false;
  }
}

function applyNativeFallbackSurface(reason = 'timeout') {
  try {
    if (fullCustomPreloadLoaded) return false;
    if (hasHealthyCustomShellMarkers()) return false;
    const body = document.body;
    if (!(body instanceof HTMLElement)) return false;
    body.classList.add('yc-native-profile-open');
    markBootstrapState(`fallback:${String(reason || 'timeout').slice(0, 48)}`);
    sendPreloadHeartbeat('bootstrap:fallback', {
      reason: String(reason || 'timeout').slice(0, 120)
    });
    logBootstrapTrace('native-fallback-applied', {
      reason: String(reason || 'timeout').slice(0, 120)
    });
    window.setTimeout(() => {
      if (hasVisibleNativeSurfaceContent()) return;
      ensureFatalBanner(
        'Экран входа не загрузился. Проверьте доступ к yuchat.rt.ru и sso.keyid.rt.ru, затем перезапустите YuChat.'
      );
    }, 2200);
    return true;
  } catch {
    return false;
  }
}

function scheduleNativeFallbackSurface() {
  const runFallback = () => {
    clearNativeFallbackSurfaceTimer();
    nativeFallbackTimer = window.setTimeout(() => {
      nativeFallbackTimer = 0;
      applyNativeFallbackSurface('preboot-timeout');
    }, PREBOOT_FALLBACK_TIMER_MS);
  };
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', runFallback, { once: true });
  } else {
    runFallback();
  }
}

const windowRole = getWindowRoleFromArgv();
if (CUSTOM_PRELOAD_BYPASS_ROLES.has(windowRole)) {
  markBootstrapState(`skipped:${windowRole}`);
  sendPreloadHeartbeat('bootstrap:skipped', {
    role: windowRole
  });
  logBootstrapTrace('bootstrap-skipped-for-role', {
    role: windowRole
  });
} else {
  ensurePrebootStyle();
  markBootstrapState('1');
  scheduleNativeFallbackSurface();
  sendPreloadHeartbeat('bootstrap:start', {
    preloadPath: FULL_CUSTOM_PRELOAD_MODULE_PATH
  });
  logBootstrapTrace('style-installed', {
    path: FULL_CUSTOM_PRELOAD_MODULE_PATH
  });

  try {
    logBootstrapTrace('require-full-preload:start');
    require(FULL_CUSTOM_PRELOAD_MODULE_PATH);
    fullCustomPreloadLoaded = true;
    clearNativeFallbackSurfaceTimer();
    markBootstrapState('loaded');
    sendPreloadHeartbeat('bootstrap:loaded');
    logBootstrapTrace('require-full-preload:ok');
  } catch (error) {
    document.body?.classList.remove('yc-native-profile-open');
    ensurePrebootStyle();
    markBootstrapState('failed');
    ensureFatalBanner(
      `Кастомная оболочка YuChat не запустилась: ${String(error?.message || error || 'unknown error').slice(0, 220)}`
    );
    sendPreloadHeartbeat('bootstrap:failed', {
      error: String(error?.message || error || 'unknown error').slice(0, 220)
    });
    logBootstrapTrace('require-full-preload:failed', {
      message: String(error?.message || error || 'unknown error').slice(0, 220)
    });
    console.error('[YuChat] Failed to load full custom preload:', error);
  }
}
