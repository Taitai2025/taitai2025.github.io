(function () {
  const mount = document.getElementById("mount-social") || document.body;
  mount.insertAdjacentHTML("beforeend", `
  <div id="social">
    <button id="toggle-btn-social">
      <span><i class="fas fa-sun"></i></span>
    </button>
    <div id="clock-social">GMT+8 00:00</div>

    <div class="container">
      <div class="social-heading" data-i18n="social_heading">Connect With Me</div>

      <div class="social-grid">
        <div class="social-card">
          <div class="social-icon">
            <svg class="bilibili-icon" viewBox="0 0 24 24" aria-hidden="true" xmlns="http://www.w3.org/2000/svg">
              <path d="M17.99 6.5a2 2 0 0 1 2 2v7a2 2 0 0 1-2 2H6.01a2 2 0 0 1-2-2v-7a2 2 0 0 1 2-2h2.75l-1-3a.5.5 0 0 1 .33-.63l.94-.3a.5.5 0 0 1 .63.32l1.1 3.1h2.64l1.1-3.1a.5.5 0 0 1 .63-.32l.94.3a.5.5 0 0 1 .33.63l-1 3h2.75zm-2.74 2.5H8.75a1.5 1.5 0 0 0-1.5 1.5v3a1.5 1.5 0 0 0 1.5 1.5h6.5a1.5 1.5 0 0 0 1.5-1.5v-3a1.5 1.5 0 0 0-1.5-1.5z"
                    fill="currentColor" stroke="currentColor" stroke-width="0.2"/>
              <circle cx="10.5" cy="11.5" r="1" fill="currentColor"/>
              <circle cx="13.5" cy="11.5" r="1" fill="currentColor"/>
            </svg>
          </div>
          <div class="social-title" data-i18n="bilibili_title">Bilibili</div>
          <div class="social-description" data-i18n="bilibili_desc">Chinese video platform for my content</div>
          <a href="https://space.bilibili.com/302136349" class="social-link" target="_blank" rel="noopener" data-i18n="link_channel">Channel</a>
        </div>

        <div class="social-card">
          <div class="social-icon"><i class="fas fa-book"></i></div>
          <div class="social-title" data-i18n="rednote_title">REDnote</div>
          <div class="social-description" data-i18n="rednote_desc">Lifestyle notes and sharing</div>
          <a href="https://www.xiaohongshu.com/user/profile/65fe92070000000017006570" class="social-link" target="_blank" rel="noopener" data-i18n="link_profile">Profile</a>
        </div>

        <div class="social-card">
          <div class="social-icon"><i class="fas fa-comments"></i></div>
          <div class="social-title" data-i18n="zhihu_title">Zhihu</div>
          <div class="social-description" data-i18n="zhihu_desc">Questions, answers, and longer posts</div>
          <a href="https://www.zhihu.com/people/tttttt-90-22" class="social-link" target="_blank" rel="noopener" data-i18n="link_profile">Profile</a>
        </div>

        <div class="social-card">
          <div class="social-icon"><i class="fab fa-github"></i></div>
          <div class="social-title" data-i18n="github_title">GitHub</div>
          <div class="social-description" data-i18n="github_desc">Repositories and ongoing projects</div>
          <a href="https://github.com/Taitai2025" class="social-link" target="_blank" rel="noopener" data-i18n="link_profile">Profile</a>
        </div>
      </div>
    </div>

    <div class="container stats-container">
      <div class="stats-heading" data-i18n="stats_heading">Website Statistics</div>

      <div class="stats-metrics" aria-label="Statistics summary">
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_site_pv">Site page views</div>
          <div class="stats-metric-value"><span id="busuanzi_value_site_pv">—</span></div>
        </div>
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_site_uv">Site visitors</div>
          <div class="stats-metric-value"><span id="busuanzi_value_site_uv">—</span></div>
        </div>
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_page_pv">This page views</div>
          <div class="stats-metric-value"><span id="busuanzi_value_page_pv">—</span></div>
        </div>
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_path">Current path</div>
          <div class="stats-metric-value stats-path-value" id="stats-current-path">/</div>
        </div>
      </div>

      <div class="stats-block">
        <div class="stats-subtitle">
          <span data-i18n="stats_live_title">Detailed Statistics</span>
        </div>

        <div class="stats-detail-card">
          <div class="stats-detail-grid" aria-label="Detailed statistics">
            <div class="stats-detail-item">
              <div class="stats-detail-label" data-i18n="metric_site_pv">Site page views</div>
              <div class="stats-detail-value" id="stats-mirror-site-pv">—</div>
            </div>
            <div class="stats-detail-item">
              <div class="stats-detail-label" data-i18n="metric_site_uv">Site visitors</div>
              <div class="stats-detail-value" id="stats-mirror-site-uv">—</div>
            </div>
            <div class="stats-detail-item">
              <div class="stats-detail-label" data-i18n="metric_page_pv">This page views</div>
              <div class="stats-detail-value" id="stats-mirror-page-pv">—</div>
            </div>
            <div class="stats-detail-item">
              <div class="stats-detail-label" data-i18n="metric_path">Current path</div>
              <div class="stats-detail-value stats-detail-path" id="stats-mirror-path">/</div>
            </div>
          </div>

          <div class="stats-service-strip">
            <span class="stats-service-badge" data-i18n="stats_service_busuanzi">Busuanzi Counter</span>
            <span class="stats-service-badge stats-service-badge-soft" data-i18n="stats_service_active">Live</span>
            <div class="stats-service-note" data-i18n="stats_live_body">The summary cards above and the detail grid here are both powered by the live counter integration. If a browser blocker prevents loading the script, the values may stay as —.</div>
          </div>
        </div>
      </div>

      <div class="stats-sep"></div>

      <div class="stats-block">
        <div class="stats-subtitle">
          <span data-i18n="visitor_map">Visitor Map</span>
          <a class="stats-link" id="visitor-map-open" target="_blank" rel="noopener" data-i18n="link_open_map">Open</a>
        </div>
        <div class="clustrmaps-wrap visitor-map-frame">
          <a id="visitor-map-anchor" class="visitor-map-anchor" target="_blank" rel="noopener">
            <img id="visitor-map-image" class="visitor-map-image" alt="Visitor map">
          </a>
          <div id="visitor-map-fallback" class="stats-embed-fallback" hidden data-i18n="stats_embed_fail">The external visitor map could not be loaded. Check your network access or a blocker.</div>
        </div>
        <div class="stats-note" data-i18n="visitor_body">The map is now live. Click it to view a larger geographic breakdown in a new tab.</div>
        <div class="stats-provider-line">
          <a href="https://smallcounter.com" target="_blank" rel="noopener" data-i18n="provider_smallcounter">map counter</a>
        </div>
      </div>
    </div>
  </div>
`);
})();

(function () {
  const BUSUANZI_SCRIPT = 'https://busuanzi.ibruce.info/busuanzi/2.3/busuanzi.pure.mini.js';
  const SMALLCOUNTER_ID = '1775458611';
  const SMALLCOUNTER_MAP_HREF = `https://smallcounter.com/vmap/${SMALLCOUNTER_ID}/`;
  const SMALLCOUNTER_MAP_SRC = `https://smallcounter.com/map/view.php?type=180&id=${SMALLCOUNTER_ID}`;

  let mirrorTimer = null;

  function normalizePath(pathname) {
    const clean = String(pathname || '/').replace(/\/+/g, '/');
    if (!clean || clean === '') return '/';
    return clean;
  }

  function setCurrentPath() {
    const path = normalizePath(window.location.pathname || '/');
    const topPath = document.getElementById('stats-current-path');
    const mirrorPath = document.getElementById('stats-mirror-path');
    if (topPath) topPath.textContent = path;
    if (mirrorPath) mirrorPath.textContent = path;
  }

  function injectBusuanzi() {
    if (document.getElementById('busuanzi-script')) return;
    const s = document.createElement('script');
    s.id = 'busuanzi-script';
    s.async = true;
    s.src = BUSUANZI_SCRIPT;
    document.head.appendChild(s);
  }

  function mirrorMetric(sourceId, targetId) {
    const src = document.getElementById(sourceId);
    const dst = document.getElementById(targetId);
    if (!dst) return;
    const val = src && String(src.textContent || '').trim() ? String(src.textContent || '').trim() : '—';
    dst.textContent = val;
  }

  function syncMetricMirrors() {
    mirrorMetric('busuanzi_value_site_pv', 'stats-mirror-site-pv');
    mirrorMetric('busuanzi_value_site_uv', 'stats-mirror-site-uv');
    mirrorMetric('busuanzi_value_page_pv', 'stats-mirror-page-pv');
    setCurrentPath();
  }

  function configureVisitorMap() {
    const anchor = document.getElementById('visitor-map-anchor');
    const openLink = document.getElementById('visitor-map-open');
    const img = document.getElementById('visitor-map-image');
    const fallback = document.getElementById('visitor-map-fallback');

    if (anchor) anchor.href = SMALLCOUNTER_MAP_HREF;
    if (openLink) openLink.href = SMALLCOUNTER_MAP_HREF;

    if (!img) return;
    img.src = SMALLCOUNTER_MAP_SRC;

    img.addEventListener('error', () => {
      if (anchor) anchor.style.display = 'none';
      if (fallback) fallback.hidden = false;
    }, { once: true });
  }

  function setVisitorMapA11y() {
    const lang = (window.SiteLang && typeof window.SiteLang.getLang === 'function')
      ? window.SiteLang.getLang()
      : 'en';

    const img = document.getElementById('visitor-map-image');
    const openLink = document.getElementById('visitor-map-open');
    const anchor = document.getElementById('visitor-map-anchor');

    const altText = lang === 'zh' ? '访客地图' : 'Visitor map';
    const titleText = lang === 'zh' ? '打开访客地图' : 'Open visitor map';

    if (img) {
      img.alt = altText;
      img.title = titleText;
    }
    if (openLink) {
      openLink.setAttribute('aria-label', titleText);
      openLink.title = titleText;
    }
    if (anchor) {
      anchor.setAttribute('aria-label', titleText);
      anchor.title = titleText;
    }
  }

  function startMirrorLoop() {
    if (mirrorTimer) return;
    mirrorTimer = window.setInterval(syncMetricMirrors, 1000);
  }

  window.addEventListener('load', () => {
    setCurrentPath();
    injectBusuanzi();
    configureVisitorMap();
    setVisitorMapA11y();
    syncMetricMirrors();
    startMirrorLoop();
  }, { once: true });

  window.addEventListener('site:langchange', () => {
    setCurrentPath();
    setVisitorMapA11y();
    syncMetricMirrors();
  });
})();
