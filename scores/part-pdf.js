(() => {
  const index = document.querySelector('[data-part-work]');
  if (!index) return;

  const raw = 'https://raw.githubusercontent.com/Taitai2025/taitai2025.github.io/score-pdf-files/';
  const validPath = /^parts\/([a-z0-9-]+)\/([a-z0-9-]+)-[a-f0-9]{16}\/(\d{4})\.pdf$/;
  const tags = new Set(index.dataset.partTags.split(' '));
  const slug = index.dataset.partWork;
  const template = index.querySelector('[data-part-pdf-preview]');
  const records = new WeakMap();
  let dialog;
  let objectUrl;
  let request;

  function resetPreview() {
    request?.abort();
    if (dialog) dialog.querySelector('iframe').removeAttribute('src');
    if (objectUrl) URL.revokeObjectURL(objectUrl);
    objectUrl = undefined;
  }

  async function showPreview(link, record) {
    if (!dialog) {
      index.append(template.content.cloneNode(true));
      dialog = index.querySelector('dialog');
      dialog.addEventListener('close', resetPreview);
    }
    if (dialog.open) return;
    const title = dialog.querySelector('#part-pdf-title');
    const status = dialog.querySelector('#part-pdf-status');
    const frame = dialog.querySelector('iframe');
    const download = dialog.querySelector('[data-part-pdf-download]');
    const newTab = dialog.querySelector('[data-part-pdf-new-tab]');
    title.textContent = record.filename;
    status.textContent = '正在读取 PDF…';
    frame.hidden = true;
    download.href = link.href;
    download.removeAttribute('download');
    newTab.hidden = true;
    newTab.removeAttribute('href');
    const controller = new AbortController();
    request = controller;
    dialog.showModal();
    try {
      const response = await fetch(link.href, {
        signal: controller.signal,
        referrerPolicy: 'no-referrer',
      });
      if (!response.ok) throw new Error('PDF unavailable');
      const bytes = await response.arrayBuffer();
      const header = new Uint8Array(bytes, 0, Math.min(bytes.byteLength, 5));
      if (bytes.byteLength !== record.bytes || String.fromCharCode(...header) !== '%PDF-') {
        throw new Error('PDF does not match the catalogue');
      }
      const hash = await crypto.subtle.digest('SHA-256', bytes);
      const actual = Array.from(new Uint8Array(hash), byte => byte.toString(16).padStart(2, '0')).join('');
      if (actual !== record.sha256) throw new Error('PDF checksum differs from the catalogue');
      if (controller.signal.aborted) return;

      objectUrl = URL.createObjectURL(new Blob([bytes], {type: 'application/pdf'}));
      frame.src = objectUrl;
      frame.hidden = false;
      download.href = objectUrl;
      download.download = record.filename;
      newTab.href = objectUrl;
      newTab.hidden = false;
      status.textContent = '如浏览器提示，请输入该版原有 PDF 口令。';
    } catch (error) {
      if (controller.signal.aborted) return;
      status.textContent = '暂时无法在线查看。下载后可用原有口令打开。';
    }
  }

  index.addEventListener('click', event => {
    const link = event.target.closest('[data-part-pdf-link]');
    if (!link || !records.has(link) || !navigator.pdfViewerEnabled || !crypto.subtle
      || typeof HTMLDialogElement.prototype.showModal !== 'function'
      || event.defaultPrevented || event.button !== 0 || event.ctrlKey
      || event.metaKey || event.shiftKey || event.altKey) return;
    event.preventDefault();
    void showPreview(link, records.get(link));
  });

  async function addPublishedLinks() {
    try {
      const response = await fetch(raw + 'scores/data/direct-parts.json', {referrerPolicy: 'no-referrer'});
      if (!response.ok) return;
      const manifest = await response.json();
      if (!manifest || !Object.hasOwn(manifest, slug)) return;
      const parts = manifest[slug];
      if (!parts || typeof parts !== 'object') return;
      for (const row of index.querySelectorAll('[data-filename][data-part-pages]')) {
        const filename = row.dataset.filename;
        if (!Object.hasOwn(parts, filename)) continue;
        const part = parts[filename];
        if (!part || typeof part.path !== 'string') continue;
        const path = validPath.exec(part.path);
        if (!path || path[1] !== slug || !tags.has(path[2]) || Number(path[3]) === 0
          || !Number.isSafeInteger(part.bytes) || part.bytes < 5
          || part.pages !== Number(row.dataset.partPages)
          || typeof part.sha256 !== 'string' || !/^[a-f0-9]{64}$/.test(part.sha256)
          || row.querySelector('[data-part-pdf-link]')) continue;
        const link = document.createElement('a');
        link.className = 'button part-pdf-link';
        link.href = raw + part.path;
        link.setAttribute('aria-label', '打开 PDF ' + filename);
        link.setAttribute('data-part-pdf-link', '');
        link.textContent = '打开 PDF';
        records.set(link, {...part, filename});
        row.append(link);
      }
    } catch (error) {
      // ZIP downloads stay usable when the separate publication is unavailable.
    }
  }

  void addPublishedLinks();
})();
