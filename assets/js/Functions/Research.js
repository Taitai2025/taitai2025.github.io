(function () {
  'use strict';
  const mount = document.getElementById('mount-research');
  mount.innerHTML = '<main id="research" aria-label="Research and writing"><div class="container"></div></main>';

  const repo = 'https://github.com/Taitai2025/taitai2025.github.io/tree/main/research';
  const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const notes = [
    {
      id: 'lmsd-sweep-proof-note',
      zh: '秩压缩 LMSD 的整轮收敛',
      en: 'Convergence of rank-compressed LMSD sweeps',
      source: 'lmsd',
      pages: 14
    },
    {
      id: 'spectral-reading-note',
      zh: '谱梯度法的端点动力学',
      en: 'Endpoint dynamics of spectral gradient methods',
      source: 'spectral',
      pages: 6
    }
  ];
  const topics = [
    {id:'spectral', zh:'谱步长与 BB 方法', en:'Spectral steps and BB methods',
     groups:['BB 谱步长','谱梯度与周期切换','谱步长与 BB 方法']},
    {id:'ritz', zh:'LMSD 与 Ritz 方法', en:'LMSD and Ritz methods',
     groups:['LMSD 与 Ritz 重用','谱梯度与 Ritz','LMSD 与 Ritz 方法','延迟记忆与 Ritz']},
    {id:'stepsizes', zh:'曲率、线搜索与停止', en:'Curvature, line search, and stopping',
     groups:['曲率信息与步长','重启、投影与线搜索','步长设计与停止条件']},
    {id:'low-rank', zh:'矩阵分解与 ADMM', en:'Matrix decomposition and ADMM',
     groups:['低秩分解','ADMM 与参数选择','分裂法与矩阵分解']},
    {id:'numerical-range', zh:'数值域与共形映射', en:'Numerical ranges and conformal maps',
     groups:['数值域与共形映射']},
    {id:'design', zh:'最优实验设计', en:'Optimal experimental design', groups:['最优实验设计']}
  ];

  function link(url, label, options = {}) {
    const attr = options.download ? 'download' : 'target="_blank" rel="noopener noreferrer"';
    const icon = options.download ? '↓' : '↗';
    return `<a class="document-link${options.primary ? ' research-pdf' : ''}" href="${esc(url)}" ${attr}>${esc(label)} <span aria-hidden="true">${icon}</span></a>`;
  }

  function entry({id, title, meta, description, links, scope = '', extra = '', related = '', heading = 'h3'}) {
    return `<article class="research-entry"${id ? ` id="${esc(id)}"` : ''}>
      <div class="research-entry-main">
        <${heading}>${esc(title)}</${heading}>
        ${meta ? `<p class="research-meta">${esc(meta)}</p>` : ''}
        ${description ? `<p class="research-result">${esc(description)}</p>` : ''}
        ${scope ? `<p class="research-scope">${esc(scope)}</p>` : ''}
        ${extra}${related}
      </div>
      <div class="research-entry-links">${links}</div>
    </article>`;
  }

  const readPdf = (url, zh) => link(url, zh ? '阅览 PDF' : 'Read PDF', {primary:true});
  function protectedPdf(id, zh, label, title, kind = 'pdf') {
    return `<button type="button" class="document-link research-pdf research-protected" data-protected-document="${esc(id)}" data-document-kind="${esc(kind)}" data-document-lang="${zh ? 'zh' : 'en'}" data-document-title="${esc(title || label || '')}" aria-haspopup="dialog"><span aria-hidden="true">🔒</span> ${esc(label || (zh ? '密码阅览 PDF' : 'Unlock PDF'))}</button>`;
  }

  // The public site contains only encrypted bytes. Passwords stay in this browser
  // for the current unlock attempt and are never stored or sent to a server.
  let unlockDialog;
  let unlockAttempt = 0;
  let unlockRequest;
  let unlockedUrl;
  let unlockTrigger;

  function releaseUnlockedFile() {
    if (unlockedUrl) {
      window.URL.revokeObjectURL(unlockedUrl);
      unlockedUrl = undefined;
    }
  }

  function closeUnlock() {
    unlockAttempt += 1;
    if (unlockRequest) unlockRequest.abort();
    releaseUnlockedFile();
    if (unlockDialog) {
      unlockDialog.querySelector('input').value = '';
      unlockDialog.querySelector('.research-unlock-result').hidden = true;
      unlockDialog.querySelectorAll('.research-unlock-result a').forEach(a => a.removeAttribute('href'));
    }
  }

  function openUnlock(trigger) {
    const id = trigger.dataset.protectedDocument;
    if (!/^[a-z0-9-]+$/.test(id || '')) return;
    const zh = trigger.dataset.documentLang === 'zh';
    const isArchive = trigger.dataset.documentKind === 'zip';
    const extension = isArchive ? 'zip' : 'pdf';
    const magic = isArchive ? 'RZIP1' : 'RPDF1';
    closeUnlock();
    unlockTrigger = trigger;
    if (!unlockDialog) {
      unlockDialog = document.createElement('dialog');
      unlockDialog.className = 'research-unlock-dialog';
      unlockDialog.setAttribute('aria-labelledby', 'research-unlock-title');
      unlockDialog.setAttribute('aria-describedby', 'research-unlock-explanation');
      unlockDialog.addEventListener('close', () => {
        closeUnlock();
        if (unlockTrigger && unlockTrigger.isConnected) unlockTrigger.focus();
      });
      document.body.appendChild(unlockDialog);
    }
    unlockDialog.lang = zh ? 'zh-CN' : 'en';
    unlockDialog.innerHTML = `<form class="research-unlock-form">
      <h2 id="research-unlock-title">${zh ? '密码阅览' : 'Unlock this file'}</h2>
      <p class="research-unlock-document">${esc(trigger.dataset.documentTitle)}</p>
      <p id="research-unlock-explanation">${isArchive
        ? (zh ? '输入阅读密码，在本机解密并下载源码与核验附件。' : 'Enter the reading password to decrypt and download the source and verification files on this device.')
        : (zh ? '这份 AI 辅助稿件尚待作者人工核阅。输入密码后可在本机解密并打开 PDF。' : 'This AI-assisted draft awaits the author’s review. Enter the password to decrypt and open the PDF on this device.')}</p>
      <label for="research-unlock-password">${zh ? '阅览密码' : 'Reading password'}</label>
      <input id="research-unlock-password" name="password" type="password" autocomplete="off" autocapitalize="none" spellcheck="false" required aria-describedby="research-unlock-status">
      <div class="research-unlock-actions">
        <button type="button" class="research-unlock-close">${zh ? '关闭' : 'Close'}</button>
        <button type="submit" class="research-unlock-submit">${isArchive ? (zh ? '解锁附件' : 'Unlock archive') : (zh ? '解锁 PDF' : 'Unlock PDF')}</button>
      </div>
      <p id="research-unlock-status" class="research-unlock-status" role="status" aria-live="polite" aria-atomic="true"></p>
      <div class="research-unlock-result" hidden>
        ${isArchive ? '' : `<a class="document-link research-unlock-open" target="_blank" rel="noopener">${zh ? '打开 PDF ↗' : 'Open PDF ↗'}</a>`}
        <a class="document-link research-unlock-download" download="${esc(id)}.${extension}">${isArchive ? (zh ? '下载附件 ZIP ↓' : 'Download ZIP ↓') : (zh ? '下载 PDF ↓' : 'Download PDF ↓')}</a>
        <p>${isArchive
          ? (zh ? '下载后可在本机解压。已保存的副本可直接读取。' : 'Extract the downloaded archive on this device. Saved copies remain readable.')
          : (zh ? '若浏览器无法预览，请下载后在 PDF 阅读器中打开。关闭此窗口会清除本次解锁；已保存的副本仍可读取。' : 'If preview is unavailable, download the file and open it in a PDF reader. Closing this dialog clears this unlock; saved copies remain readable.')}</p>
      </div>
    </form>`;
    const input = unlockDialog.querySelector('input');
    const form = unlockDialog.querySelector('form');
    const status = unlockDialog.querySelector('.research-unlock-status');
    const submit = unlockDialog.querySelector('[type="submit"]');
    unlockDialog.querySelector('.research-unlock-close').addEventListener('click', () => unlockDialog.close());
    form.addEventListener('submit', async event => {
      event.preventDefault();
      if (submit.disabled || !input.value) return;
      const attempt = ++unlockAttempt;
      const password = input.value;
      input.value = '';
      input.removeAttribute('aria-invalid');
      status.dataset.state = 'busy';
      status.textContent = zh ? '正在解锁，请稍候……' : 'Unlocking, please wait…';
      submit.disabled = true;
      form.setAttribute('aria-busy', 'true');
      releaseUnlockedFile();
      unlockDialog.querySelector('.research-unlock-result').hidden = true;
      unlockRequest = new AbortController();
      let passwordBytes;
      try {
        if (!window.crypto?.subtle || !window.TextEncoder) throw new Error('unsupported');
        const response = await fetch('assets/documents/protected/' + id + '.r' + extension, {signal: unlockRequest.signal, cache: 'no-store'});
        if (!response.ok) throw new Error('download');
        const packet = new Uint8Array(await response.arrayBuffer());
        if (packet.length < 54 || String.fromCharCode(...packet.subarray(0, 5)) !== magic) throw new Error('format');
        passwordBytes = new TextEncoder().encode(password);
        const material = await window.crypto.subtle.importKey('raw', passwordBytes, 'PBKDF2', false, ['deriveKey']);
        const key = await window.crypto.subtle.deriveKey(
          {name: 'PBKDF2', salt: packet.slice(5, 21), iterations: 600000, hash: 'SHA-256'},
          material, {name: 'AES-GCM', length: 256}, false, ['decrypt']
        );
        const plaintext = new Uint8Array(await window.crypto.subtle.decrypt(
          {name: 'AES-GCM', iv: packet.slice(21, 33), tagLength: 128}, key, packet.slice(33)
        ));
        if (attempt !== unlockAttempt || !unlockDialog.open) { plaintext.fill(0); return; }
        const signature = isArchive ? 'PK\x03\x04' : '%PDF-';
        if (String.fromCharCode(...plaintext.subarray(0, signature.length)) !== signature) {
          plaintext.fill(0);
          throw new Error('format');
        }
        const type = isArchive ? 'application/zip' : 'application/pdf';
        unlockedUrl = window.URL.createObjectURL(new Blob([plaintext], {type}));
        plaintext.fill(0);
        unlockDialog.querySelectorAll('.research-unlock-result a').forEach(a => { a.href = unlockedUrl; });
        unlockDialog.querySelector('.research-unlock-result').hidden = false;
        status.dataset.state = 'success';
        status.textContent = isArchive
          ? (zh ? '已解锁。可以下载附件。' : 'Unlocked. The archive is ready to download.')
          : (zh ? '已解锁。请选择打开或下载 PDF。' : 'Unlocked. Choose Open PDF or Download PDF below.');
        unlockDialog.querySelector(isArchive ? '.research-unlock-download' : '.research-unlock-open').focus();
      } catch (error) {
        if (attempt !== unlockAttempt || error.name === 'AbortError') return;
        status.dataset.state = 'error';
        if (error.message === 'unsupported') {
          status.textContent = zh ? '此浏览器无法安全解密。请用较新版本的浏览器通过 HTTPS 打开本页。' : 'Secure decryption is unavailable. Open this page over HTTPS in a current browser.';
        } else if (error.message === 'download' || error instanceof TypeError) {
          status.textContent = zh ? '文件暂时无法下载，请检查网络后重试。' : 'The file could not be downloaded. Check your connection and try again.';
        } else if (error.message === 'format') {
          status.textContent = zh ? '文件格式有误，暂时无法打开。请联系作者。' : 'This file could not be opened. Please contact the author.';
        } else {
          status.textContent = zh ? '密码不正确，或文件校验未通过。请重新输入密码。' : 'The password is incorrect, or the file could not be verified. Please try again.';
          input.setAttribute('aria-invalid', 'true');
        }
        input.focus();
      } finally {
        if (passwordBytes) passwordBytes.fill(0);
        if (attempt === unlockAttempt) {
          submit.disabled = false;
          form.removeAttribute('aria-busy');
        }
      }
    });
    unlockDialog.showModal();
    input.focus();
  }

  window.addEventListener('pagehide', closeUnlock);

  function papersSection(data, zh) {
    const cards = data.papers.map(p => {
      const links = link('https://arxiv.org/abs/' + p.id, 'arXiv', {primary:true}) +
        (p.file ? link(p.file, zh ? '预印本 PDF' : 'Preprint PDF') : '') +
        (p.manuscript ? link(p.manuscript, zh ? '作者稿' : 'Author manuscript') : '');
      const citation = p.authors + '. ' + p.title + '. arXiv:' + p.id + ' (2026).';
      return entry({
        id: 'preprint-' + p.id,
        title: p.title,
        meta: [p.authors, p.date, 'arXiv:' + p.id].join(' · '),
        description: zh ? p.zh : p.en,
        links,
        extra: `<details class="research-citation"><summary>${zh ? '引用信息' : 'Citation'}</summary><p>${esc(citation)}</p></details>`
      });
    }).join('');
    return `<section id="research-papers" class="research-section">
      <h2>${zh ? '研究论文与预印本' : 'Papers and preprints'}</h2>
      ${cards}
    </section>`;
  }

  function archiveSection(data, zh) {
    const drafts = data.working || [];
    const fullTexts = data.manuscripts || [];
    const entries = fullTexts.map(p => ({p, full:true})).concat(drafts.map(p => ({p, full:false})));
    const byId = new Map(drafts.map(p => [p.id, p]));
    const cards = ({p, full}) => {
      const links = protectedPdf(p.id, zh, undefined, zh ? p.zh : p.en) +
        (p.arxiv ? link(p.arxiv, zh ? '相关 arXiv 版本' : 'Related arXiv version') : '') +
        (p.guide ? protectedPdf(p.guide.replace(/\.pdf$/i, ''), zh, zh ? p.guideZh : p.guideEn, zh ? p.guideZh : p.guideEn) : '') +
        (p.archive ? protectedPdf(p.id, zh, zh ? '密码下载附件' : 'Unlock source archive', zh ? p.zh : p.en, 'zip') : '');
      const related = (p.related || []).filter(id => byId.has(id)).map(id =>
        `<a href="#working-${esc(id)}">${esc(zh ? byId.get(id).zh : byId.get(id).en)}</a>`).join(' · ');
      const pages = zh ? `${p.pages} 页` : `${p.pages} pages`;
      const meta = full
        ? [zh ? '全文整理版' : 'Archived full text', zh ? `${pages}正文，另附版本说明` : `${pages} of manuscript, plus a cover note`]
        : [`v${p.version}`, p.releaseDate || '2026.11.25', pages];
      return entry({
        id: (full ? 'manuscript-' : 'working-') + p.id,
        title: zh ? p.zh : p.en,
        meta: meta.join(' · '),
        description: '',
        links,
        heading: 'h4',
        related: related ? `<p class="research-related">${zh ? '相关稿件' : 'Related papers'} · ${related}</p>` : ''
      });
    };

    if (!entries.length) return '';
    const section = (id, label, items) => items.length
      ? `<section class="research-work-group" aria-labelledby="research-topic-${id}">
          <h3 id="research-topic-${id}">${esc(label)}</h3>${items.map(cards).join('')}
         </section>`
      : '';
    const categorized = new Set(topics.flatMap(t => t.groups));
    const visibleTopics = topics.map(topic => ({
      ...topic,
      items: entries.filter(({p}) => topic.groups.includes(p.groupZh))
    })).filter(topic => topic.items.length);
    const ungrouped = entries.filter(({p}) => !categorized.has(p.groupZh));
    if (ungrouped.length) visibleTopics.push({id:'other', zh:'其他研究', en:'Other research', items:ungrouped});
    const groups = visibleTopics.map(topic =>
      section(topic.id, zh ? topic.zh : topic.en, topic.items)).join('');
    const notice = zh
      ? '以下工作稿经 AI 辅助整理，尚待作者逐项人工核阅。标题与版本信息公开保留，全文需输入密码阅览。'
      : 'These AI-assisted working papers await the author’s review. Titles and version details remain public; a password is required to read the full text.';
    return `<section id="research-working" class="research-section">
      ${fullTexts.length ? '<span id="research-manuscripts" class="research-section-anchor" aria-hidden="true"></span>' : ''}
      <h2>${zh ? 'AI 辅助研究工作稿' : 'AI-assisted research working papers'}</h2>
      <p class="research-disclosure">${esc(notice)}</p>
      <nav class="research-topic-links" aria-label="${zh ? '工作稿主题' : 'Working-paper topics'}">
        ${visibleTopics.map(t => `<a href="#research-topic-${t.id}">${esc(zh ? t.zh : t.en)}</a>`).join('')}
      </nav>
      ${groups}
    </section>`;
  }

  function readingSection(zh) {
    return `<section id="research-reading" class="research-section">
      <h2>${zh ? '研究导读与复现' : 'Reading notes and reproducibility'}</h2>
      <p class="research-section-note">${zh
        ? '导读经 AI 辅助整理，待作者核阅。全文需输入密码阅览；研究结论请引用原始预印本。'
        : 'These AI-assisted reading notes await author review and require a password. Cite the original preprints for research results.'}</p>
      ${notes.map(n => entry({
        id: 'reading-' + n.id,
        title: zh ? n.zh : n.en,
        description: '',
        meta: zh ? `中文导读 · ${n.pages} 页` : `Reading note in Chinese · ${n.pages} pages`,
        links: protectedPdf(n.id, zh, undefined, zh ? n.zh : n.en)
      })).join('')}
    </section>`;
  }

  function earlierSection(id, title, items, zh) {
    return `<section id="${id}" class="research-section"><h2>${esc(title)}</h2>
      ${items.map(i => entry({
        title:i.title, meta:i.meta, description:zh ? i.zh : i.en,
        links:(i.file ? readPdf(i.file,zh) : '') +
          (i.manuscript ? link(i.manuscript, zh ? '作者稿' : 'Manuscript') : '') +
          (i.projectNotice ? link(i.projectNotice, zh ? '项目立项通知（节选）' : 'Project approval (excerpt)') : '') +
          (i.url ? link(i.url, zh ? '原文' : 'Source') : '')
      })).join('')}
    </section>`;
  }

  function render(lang) {
    const zh = lang === 'zh';
    const data = window.RESEARCH_CONTENT;
    if (!data) return;
    const toc = [
      ['research-papers',zh ? '论文与预印本' : 'Papers and preprints'],
      ['research-working',zh ? 'AI 辅助工作稿' : 'AI-assisted working papers'],
      ['research-reading',zh ? '导读与复现' : 'Reading notes'],
      ['research-articles',zh ? '文章与早期探索' : 'Articles and early work'],
      ['research-talks',zh ? '学位论文与报告' : 'Thesis and talks']
    ];
    const title = zh ? '科研与写作' : 'Research and writing';
    const intro = zh ? '研究数值优化，重点是谱梯度法、步长设计和收敛理论。'
      : 'I study numerical optimization, with an emphasis on spectral gradient methods, stepsize selection, and convergence.';
    const root = document.querySelector('#research .container');
    root.innerHTML = `<header class="research-introduction">
        <div><h1>${title}</h1><p>${intro}</p></div>
        ${link(repo, zh ? 'GitHub 研究目录' : 'GitHub research index')}
      </header>
      <div class="research-layout">
        <nav class="research-page-nav" aria-label="${zh ? '科研目录' : 'Research contents'}">
          ${toc.map(([id,label]) => `<a href="#${id}">${esc(label)}</a>`).join('')}
        </nav>
        <div class="research-main">
          ${papersSection(data, zh)}${archiveSection(data, zh)}${readingSection(zh)}
          ${earlierSection('research-articles', zh ? '文章与早期探索' : 'Articles and early work',data.articles,zh)}
          ${earlierSection('research-talks', zh ? '学位论文、报告与发言' : 'Thesis, talks, and reports',data.talks,zh)}
          <footer class="site-footer">${zh ? '学术交流' : 'Research correspondence'} ·
            <a href="mailto:yangshutai26@mails.ucas.ac.cn">yangshutai26@mails.ucas.ac.cn</a>
          </footer>
        </div>
      </div>`;
  }

  function decorateResume() {
    const container = document.querySelector('#resume .container');
    if (!container || container.querySelector('.resume-toc')) return;
    const sections = Array.from(container.querySelectorAll(':scope > .section'));
    const toc = document.createElement('nav');
    toc.className = 'toc resume-toc';
    toc.setAttribute('aria-label','履历目录 / Contents');
    sections.forEach((section, i) => {
      const title = section.querySelector('h2');
      if (!title) return;
      section.id = 'resume-part-' + i;
      const button = document.createElement('button');
      button.dataset.scroll = section.id;
      button.textContent = title.textContent.replace(/📜|🎓|🎵/g,'').trim();
      toc.append(button);
    });
    const hero = container.querySelector('.resume-hero');
    if (hero) hero.after(toc);
  }

  document.addEventListener('click', e => {
    const protectedButton = e.target.closest('[data-protected-document]');
    if (protectedButton) openUnlock(protectedButton);
    const button = e.target.closest('[data-scroll]');
    if (button) document.getElementById(button.dataset.scroll)?.scrollIntoView({
      behavior: window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block:'start'
    });
  });
  window.addEventListener('site:langchange', decorateResume);
  document.addEventListener('DOMContentLoaded', () => {
    render(window.SiteLang?.getLang() || 'zh');
    decorateResume();
  });
  window.Research = {render};
})();

