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
          <a href="https://space.bilibili.com/302136349" class="social-link" target="_blank" data-i18n="link_channel">Channel</a>
        </div>

        <div class="social-card">
          <div class="social-icon"><i class="fas fa-book"></i></div>
          <div class="social-title" data-i18n="rednote_title">REDnote</div>
          <div class="social-description" data-i18n="rednote_desc">Lifestyle notes and sharing</div>
          <a href="https://www.xiaohongshu.com/user/profile/65fe92070000000017006570" class="social-link" target="_blank" data-i18n="link_profile">Profile</a>
        </div>

        <div class="social-card">
          <div class="social-icon"><i class="fas fa-comments"></i></div>
          <div class="social-title" data-i18n="zhihu_title">Zhihu</div>
          <div class="social-description" data-i18n="zhihu_desc">Questions, answers, and longer posts</div>
          <a href="https://www.zhihu.com/people/tttttt-90-22" class="social-link" target="_blank" data-i18n="link_profile">Profile</a>
        </div>

        <div class="social-card">
          <div class="social-icon"><i class="fab fa-github"></i></div>
          <div class="social-title" data-i18n="github_title">GitHub</div>
          <div class="social-description" data-i18n="github_desc">Repositories and ongoing projects</div>
          <a href="https://github.com/Taitai2025" class="social-link" target="_blank" data-i18n="link_profile">Profile</a>
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
          <span data-i18n="stats_live_title">Counter status</span>
        </div>
        <div class="stats-embed stats-placeholder-box stats-live-box">
          <div class="stats-placeholder-main" data-i18n="stats_live_main">Counter enabled</div>
          <div class="stats-placeholder-sub" data-i18n="stats_live_body">After deployment, the counter will start accumulating automatically. If a browser extension blocks third-party scripts, the values may stay as —.</div>
        </div>
      </div>

      <div class="stats-sep"></div>

      <div class="stats-block">
        <div class="stats-subtitle">
          <span data-i18n="visitor_map">Visitor Map</span>
        </div>
        <div class="stats-embed stats-placeholder-box">
          <div class="stats-placeholder-main" data-i18n="visitor_placeholder">Map slot reserved</div>
          <div class="stats-placeholder-sub" data-i18n="visitor_body">The Stardust-style position is kept here, so you can replace it later with any visitor-map widget you prefer.</div>
        </div>
      </div>
    </div>
  </div>
`);
})();

(function () {
  const BUSUANZI_SCRIPT = 'https://cdn.jsdelivr.net/npm/busuanzi@2.3.0';

  function normalizePath(pathname) {
    const clean = String(pathname || '/').replace(/\/+/g, '/');
    if (!clean || clean === '') return '/';
    return clean;
  }

  function setCurrentPath() {
    const el = document.getElementById('stats-current-path');
    if (!el) return;
    el.textContent = normalizePath(window.location.pathname || '/');
  }

  function injectBusuanzi() {
    if (document.getElementById('busuanzi-script')) return;
    const s = document.createElement('script');
    s.id = 'busuanzi-script';
    s.async = true;
    s.src = BUSUANZI_SCRIPT;
    document.head.appendChild(s);
  }

  window.addEventListener('load', () => {
    setCurrentPath();
    injectBusuanzi();
  }, { once: true });

  window.addEventListener('site:langchange', () => {
    setCurrentPath();
  });
})();
