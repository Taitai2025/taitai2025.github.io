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
      <div class="stats-heading" data-i18n="stats_heading">Website Traffic</div>

      <div class="stats-metrics" aria-label="Website traffic summary">
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_site_pv">Site page views</div>
          <div class="stats-metric-value"><span id="busuanzi_value_site_pv">—</span></div>
        </div>
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_site_uv">Site visitors</div>
          <div class="stats-metric-value"><span id="busuanzi_value_site_uv">—</span></div>
        </div>
        <div class="stats-metric">
          <div class="stats-metric-label" data-i18n="metric_site_location">Site location</div>
          <div class="stats-metric-value stats-location-value" data-i18n="metric_site_location_value">Beijing, China</div>
        </div>
      </div>

      <div class="stats-detail-card stats-access-card">
        <div class="stats-access-note" data-i18n="stats_live_body">
          The two counters above start to accumulate automatically after deployment. If a browser blocker prevents the external counter script from loading, the numbers may remain as —.
        </div>

        <div class="stats-access-foot">
          <span class="stats-service-badge" data-i18n="stats_service_busuanzi">Busuanzi Counter</span>
          <span class="stats-service-badge stats-service-badge-soft" data-i18n="stats_service_active">Live</span>
          <span class="stats-path-inline">
            <span data-i18n="metric_current_path">Current path</span>
            <code id="stats-current-path">/</code>
          </span>
        </div>
      </div>
    </div>

    <a href="#" class="back-btn" id="social-back-btn">
      <i class="fas fa-arrow-left"></i>
    </a>
  </div>
`);
})();

(function () {
  const BUSUANZI_SCRIPT = 'https://busuanzi.ibruce.info/busuanzi/2.3/busuanzi.pure.mini.js';

  function normalizePath(pathname) {
    const clean = String(pathname || '/').replace(/\/+/g, '/');
    if (!clean || clean === '') return '/';
    return clean;
  }

  function setCurrentPath() {
    const path = normalizePath(window.location.pathname || '/');
    const current = document.getElementById('stats-current-path');
    if (current) current.textContent = path;
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
