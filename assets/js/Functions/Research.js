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
      descriptionZh: '从行列式公式推导整轮乘子，解释秩下降时为何能终止，以及如何得到统一的指数界。',
      descriptionEn: 'Derives the full-sweep multiplier from a determinant identity, then explains termination at rank loss and the uniform rate.',
      source: 'lmsd',
      pages: 14
    },
    {
      id: 'spectral-reading-note',
      zh: '谱梯度法的端点动力学',
      en: 'Endpoint dynamics of spectral gradient methods',
      descriptionZh: '从四篇预印本提取可单独阅读的推导，串联双端点轨道、Lyapunov 能量和 Ritz 扫掠。',
      descriptionEn: 'Works through endpoint orbits, Lyapunov energy, and Ritz sweeps using results from four related preprints.',
      source: 'spectral',
      pages: 6
    }
  ];
  const topics = [
    {id:'spectral', zh:'谱梯度与 Ritz', en:'Spectral gradients and Ritz values',
     groups:['BB 谱步长','LMSD 与 Ritz 重用','谱梯度与 Ritz','谱梯度与周期切换']},
    {id:'stepsizes', zh:'步长、线搜索与停止', en:'Stepsizes, line search, and stopping',
     groups:['曲率信息与步长','重启、投影与线搜索','步长设计与停止条件']},
    {id:'low-rank', zh:'低秩分解与 ADMM', en:'Low-rank decomposition and ADMM',
     groups:['低秩分解','ADMM 与参数选择']},
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
  const notePdf = id => 'assets/documents/research/' + id + '.pdf';

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
      const links = readPdf(notePdf(p.id), zh) +
        link(`${repo}/${full ? 'manuscripts' : 'working'}/${p.source || p.formal || p.id}`, zh ? '源码与说明' : 'Source and notes') +
        (p.arxiv ? link(p.arxiv, zh ? '相关 arXiv 版本' : 'Related arXiv version') : '') +
        (p.guide ? link('assets/documents/research/' + p.guide, zh ? p.guideZh : p.guideEn) : '');
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
        description: zh ? p.descriptionZh : p.descriptionEn,
        scope: zh ? p.scopeZh : p.scopeEn,
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
    const groups = topics.map(t => section(t.id, zh ? t.zh : t.en,
      entries.filter(({p}) => t.groups.includes(p.groupZh)))).join('');
    const other = section('other', zh ? '其他研究' : 'Other research',
      entries.filter(({p}) => !categorized.has(p.groupZh)));
    const notice = zh
      ? '以下是经 AI 辅助整理的公开工作稿，待作者逐项人工核阅。引用时请注明所用版本。'
      : 'These public working papers were prepared with AI assistance and await the author’s review. Please cite the version you use.';
    return `<section id="research-working" class="research-section">
      ${fullTexts.length ? '<span id="research-manuscripts" class="research-section-anchor" aria-hidden="true"></span>' : ''}
      <h2>${zh ? 'AI 辅助研究工作稿' : 'AI-assisted research working papers'}</h2>
      <p class="research-disclosure">${esc(notice)}</p>
      <nav class="research-topic-links" aria-label="${zh ? '工作稿主题' : 'Working-paper topics'}">
        ${topics.map(t => `<a href="#research-topic-${t.id}">${esc(zh ? t.zh : t.en)}</a>`).join('')}
      </nav>
      ${groups}${other}
    </section>`;
  }

  function readingSection(zh) {
    return `<section id="research-reading" class="research-section">
      <h2>${zh ? '研究导读与复现' : 'Reading notes and reproducibility'}</h2>
      <p class="research-section-note">${zh
        ? '导读经 AI 辅助整理，待作者核阅。原始结论以条目所引预印本为准。'
        : 'The reading notes are AI-assisted and await author review. Cite the original preprints for research results.'}</p>
      ${notes.map(n => entry({
        id: 'reading-' + n.id,
        title: zh ? n.zh : n.en,
        description: zh ? n.descriptionZh : n.descriptionEn,
        meta: zh ? `中文导读 · ${n.pages} 页` : `Reading note in Chinese · ${n.pages} pages`,
        links: readPdf(notePdf(n.id), zh) + link(`${repo}/${n.source}`, zh ? '源码与校验' : 'Source and checks')
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

