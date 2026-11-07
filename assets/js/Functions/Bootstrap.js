/* Page routing for retained content and Stardust cover transitions. */
(function () {
  'use strict';
  const pages = ['resume', 'research', 'social', 'toolkit', 'schedule', 'meditations'];
  let current = null;
  let transition = 0;
  const reducedMotion = () => window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  async function navigate(page, updateHash = true) {
    if (!pages.includes(page) && page !== 'cover') page = 'cover';
    const version = ++transition;
    const cover = document.getElementById('cover');
    const leavingCover = current === 'cover' && page !== 'cover';
    current = page;
    if (updateHash && location.hash !== '#' + page) history.pushState(null, '', '#' + page);
    if (leavingCover) {
      cover?.classList.add('leaving');
      window.BootstrapCoverInput?.hideCoverElements();
      await new Promise(resolve => setTimeout(resolve, reducedMotion() ? 0 : 300));
      if (version !== transition) return;
    }
    pages.forEach(key => {
      const el = document.getElementById(key);
      if (!el) return;
      el.classList.toggle('visible', key === page);
      el.setAttribute('aria-hidden', String(key !== page));
      el.inert = key !== page;
    });
    if (cover) {
      cover.classList.toggle('hidden', page !== 'cover');
      cover.classList.remove('leaving');
      cover.setAttribute('aria-hidden', String(page !== 'cover'));
      cover.inert = page !== 'cover';
      if (page === 'cover') {
        cover.classList.add('visible');
        window.BootstrapCoverInput?.showCoverElements();
      } else window.BootstrapCoverInput?.hideCoverElements();
    }
    document.body.style.overflow = page === 'cover' ? 'hidden' : 'auto';
    if (page === 'cover') window.TopNav?.hide();
    else window.TopNav?.show();
    window.TopNav?.setActive(page);
    const nav = document.getElementById('top-nav');
    if (nav) nav.inert = page === 'cover';
    document.querySelectorAll('.top-nav-link').forEach(el => {
      if (el.dataset.page === page) el.setAttribute('aria-current', 'page');
      else el.removeAttribute('aria-current');
    });
    window.scrollTo({ top: 0, behavior: 'instant' });
    if (page !== 'cover' && updateHash) {
      const heading = document.querySelector('#' + page + ' h1, #' + page + ' [class$="-heading"]');
      if (heading) { heading.setAttribute('tabindex', '-1'); heading.focus({ preventScroll: true }); }
    }
    window.dispatchEvent(new CustomEvent('site:pagechange', { detail: { page } }));
  }
  function boot() {
    window.Theme?.init();
    window.TopNav?.init(navigate, () => navigate('cover'));
    window.Toolkit?.initToolkitFilter();
    window.Clock?.start();
    window.Schedule?.initSchedulePage();
    window.ProfileContact?.init();
    window.BootstrapCoverInput?.configure({ defaultPage: 'resume', showPage: navigate, isCoverHidden: () => current !== 'cover' });
    window.BootstrapCoverInput?.initAppHeightSync();
    window.BootstrapCoverInput?.bindCoverArrowAndScroll();
    document.addEventListener('click', event => {
      if (event.defaultPrevented || event.button !== 0 || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
      const a = event.target.closest('a[href^="#"]');
      if (!a) return;
      const target = a.getAttribute('href').slice(1);
      if (pages.includes(target) || target === 'cover' || a.classList.contains('back-btn')) { event.preventDefault(); navigate(target || 'cover'); }
    });
    window.addEventListener('hashchange', () => navigate(location.hash.slice(1), false));
    window.addEventListener('popstate', () => navigate(location.hash.slice(1), false));
    navigate(location.hash.slice(1) || 'cover', false);
  }
  window.SitePages = { navigate };
  if (document.readyState !== 'complete') document.addEventListener('DOMContentLoaded', boot);
  else boot();
})();
