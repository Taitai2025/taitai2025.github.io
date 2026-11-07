/* Shared PDF and link adapter. Reader implementation: Jinghao Chen, MIT. */
(function () {
  'use strict';
  let counter = 0;
  let queued = false;
  const openReaders = new Set();
  const readyLinks = new WeakSet();
  const escape = value => String(value).replace(/[&<>"']/g, char => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[char]));
  const chinese = () => (window.SiteLang?.getLang?.() || document.documentElement.lang || 'zh').startsWith('zh');
  const label = (zh, en) => chinese() ? zh : en;
  const pdf = url => /\.pdf(?:$|[?#])/i.test(url);
  function readerProfile() {
    const compact = window.matchMedia('(max-width: 768px)').matches;
    return {zoom:'page-width', spreadMode:compact ? 'none' : 'odd', pageMode:compact ? 'none' : 'bookmarks'};
  }

  function createReader(link) {
    const direct = link.dataset.pdfOriginal;
    const title = (link.closest('article')?.querySelector('h3')?.textContent || link.closest('li')?.textContent || link.textContent).trim().slice(0, 220);
    const reader = document.createElement('div');
    reader.className = 'pdf-reader resource-inline-reader';
    reader.id = 'resource-reader-' + (++counter);
    reader.hidden = true;
    reader.dataset.pdfReader = '';
    reader.dataset.pdfSrc = direct;
    const profile = readerProfile();
    reader.dataset.pdfSpreadMode = profile.spreadMode;
    reader.dataset.pdfPageMode = profile.pageMode;
    reader.innerHTML = `
      <div class="pdf-reader-actions">
        <button type="button" class="pdf-reader-action" data-pdf-fullscreen-open data-cursor="precise_select">${label('全屏阅读', 'Fullscreen')}</button>
        <a class="pdf-reader-action" href="${escape(direct)}" target="_blank" rel="noopener noreferrer" data-pdf-new-tab data-cursor="link_select">${label('新标签页打开', 'Open in new tab')}</a>
        <a class="pdf-reader-action" href="${escape(direct)}" download data-pdf-direct-link data-cursor="link_select">${label('下载 PDF', 'Download PDF')}</a>
        <button type="button" class="pdf-reader-action" data-resource-close>${label('收起阅读器', 'Close reader')}</button>
      </div>
      <div class="pdf-reader-fullscreen-bar" aria-hidden="true">
        <span class="pdf-reader-fullscreen-title">${escape(title)}</span>
        <div class="pdf-reader-fullscreen-actions">
          <a class="pdf-reader-fullscreen-link" href="${escape(direct)}" target="_blank" rel="noopener noreferrer" data-pdf-new-tab>${label('新标签页打开', 'Open in new tab')}</a>
          <button type="button" class="pdf-reader-fullscreen-close" data-pdf-fullscreen-close aria-label="${label('退出全屏', 'Exit fullscreen')}">×</button>
        </div>
      </div>
      <div class="pdf-reader-frame-shell"><iframe class="pdf-reader-frame" title="${escape(title)} PDF" loading="lazy" allow="fullscreen" allowfullscreen></iframe></div>
      <p class="pdf-reader-fallback">${label('如未能正常显示，可', 'If the preview is unavailable, ')}<a href="${escape(direct)}" target="_blank" rel="noopener noreferrer" data-pdf-direct-link>${label('直接打开原 PDF', 'open the original PDF')}</a>${label('，或使用上方下载按钮。', ' or use the download button above.')}</p>`;
    const host = link.closest('article, li, .section') || link.parentElement;
    host.appendChild(reader);
    window.PdfReader.init(reader);
    reader.querySelector('[data-resource-close]').addEventListener('click', () => toggle(reader, link, false));
    link.setAttribute('aria-controls', reader.id);
    link.setAttribute('aria-expanded', 'false');
    return reader;
  }

  function toggle(reader, link, open) {
    reader.hidden = !open;
    link.setAttribute('aria-expanded', String(open));
    if (open) {
      openReaders.add(reader);
      const profile = readerProfile();
      reader.dataset.pdfSpreadMode = profile.spreadMode;
      reader.dataset.pdfPageMode = profile.pageMode;
      window.PdfReader.configure(reader);
      window.PdfReader.load(reader);
      reader.scrollIntoView({block:'nearest', behavior:matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth'});
    } else {
      openReaders.delete(reader);
      window.PdfReader.closeFullscreen(reader);
      window.PdfReader.unload(reader);
      link.focus({preventScroll:true});
    }
  }

  function decorate(scope) {
    if (!window.PdfReader) return;
    scope.querySelectorAll('a[href]').forEach(link => {
      if (link.closest('[data-pdf-reader]') || readyLinks.has(link)) return;
      let url;
      try { url = new URL(link.dataset.pdfOriginal || link.getAttribute('href'), document.baseURI); } catch (_) { return; }
      if (url.hostname === 'orcid.org' && url.searchParams.has('orcid')) {
        url = new URL('https://orcid.org/' + url.searchParams.get('orcid'));
        link.href = url.href;
      }
      if (!['http:', 'https:', 'file:'].includes(url.protocol)) return;
      readyLinks.add(link);
      link.dataset.cursor = 'link_select';
      link.dataset.cursorFallback = 'pointer';
      if (link.hasAttribute('download')) return;
      if (url.origin !== location.origin || pdf(url.pathname)) {
        link.target = '_blank';
        link.rel = Array.from(new Set([...link.rel.split(/\s+/).filter(Boolean), 'noopener', 'noreferrer'])).join(' ');
      }
      if (!pdf(url.pathname)) return;
      // Keep a real URL for keyboard modifiers, middle-click and copy-link.
      // Local file:// cannot fetch a PDF worker; retain the browser-native PDF fallback.
      link.dataset.pdfOriginal = url.href;
      link.classList.add('resource-pdf-link');
      if (location.protocol !== 'file:' && url.origin === location.origin) {
        link.href = window.PdfReader.buildViewerUrl(url.href, readerProfile());
        link.setAttribute('aria-expanded', 'false');
        link.title = label('点击页内阅读；按住 Ctrl / Cmd 点击在新标签页打开', 'Read inline; Ctrl / Cmd-click to open in a new tab');
        let reader;
        link.addEventListener('click', event => {
          if (event.button !== 0 || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
          event.preventDefault();
          reader = reader?.isConnected ? reader : createReader(link);
          toggle(reader, link, reader.hidden);
        });
      }
    });
  }

  function schedule() {
    if (queued) return;
    queued = true;
    requestAnimationFrame(() => { queued = false; decorate(document); });
  }
  function start() {
    decorate(document);
    new MutationObserver(schedule).observe(document.body, {childList:true, subtree:true});
    function closeOpenReaders() {
      // Fullscreen readers are temporarily mounted on body. Restore them before
      // page/language replacement can leave an obsolete reader covering the site.
      window.PdfReader.closeFullscreenWithin(document).then(() => {
        openReaders.forEach(reader => {
          reader.hidden = true;
          window.PdfReader.unload(reader);
          document.querySelectorAll('[aria-controls="' + reader.id + '"]').forEach(link => link.setAttribute('aria-expanded', 'false'));
        });
        openReaders.clear();
      });
      schedule();
    }
    window.addEventListener('site:langchange', closeOpenReaders);
    window.addEventListener('site:pagechange', closeOpenReaders);
  }
  window.ResourceLinks = {refresh: () => decorate(document)};
  // defer scripts execute during "interactive", before DOMContentLoaded.
  // Let the language module capture pristine templates before attaching readers.
  if (document.readyState !== 'complete') document.addEventListener('DOMContentLoaded', start, {once:true});
  else start();
})();
