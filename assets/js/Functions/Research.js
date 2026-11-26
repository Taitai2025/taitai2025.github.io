(function () {
  'use strict';
  const mount=document.getElementById('mount-research');
  mount.innerHTML='<main id="research" aria-label="Research and writing"><div class="container"></div></main>';
  const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  function link(url,label,download=false){return '<a class="document-link" href="'+esc(url)+'" '+(download?'download':'target="_blank" rel="noopener noreferrer"')+'>'+esc(label)+(download?' ↓':' ↗')+'</a>';}
  function attachments(item,zh){return (item.file?link(item.file,zh?(item.fileLabelZh||'PDF 阅读'):(item.fileLabelEn||'Read PDF'))+link(item.file,zh?'下载':'Download',true):'')+(item.manuscript?link(item.manuscript,zh?'作者稿（归档版本） · '+item.manuscriptPages+' 页':'Author manuscript (archived version) · '+item.manuscriptPages+' pages'):'')+(item.projectNotice?link(item.projectNotice,zh?'国家级立项通知（节选）':'National project approval (excerpt)'):'')+(item.url?link(item.url,zh?'原文链接':'Source'):'');}
  function list(items,zh){return items.map((item,i)=>'<article class="paper"><div class="paper-number">'+String(i+1).padStart(2,'0')+'</div><div><h3>'+esc(item.title)+'</h3><p class="paper-meta">'+esc(item.meta)+'</p><p class="paper-summary">'+esc(zh?item.zh:item.en)+'</p>'+attachments(item,zh)+'</div></article>').join('');}
  function readingNote(zh){
    const notes = [
      {
        zh: '有限记忆谱梯度法的完整扫掠、秩退化与统一指数收敛',
        en: 'Complete sweeps, rank loss, and uniform exponential convergence',
        typeZh: '中文证明阅读稿 · 14 页',
        typeEn: 'Proof reading note in Chinese · 14 pages',
        descriptionZh: '逐步推导秩压缩 LMSD 的整轮乘子、退化端点与统一指数界，附三维精确算例和 Lean 文件。',
        descriptionEn: 'A worked proof of the complete-sweep multiplier, the rank-loss boundary, and the uniform rate, with an exact example and Lean files.',
        file: 'lmsd-sweep-proof-note.pdf',
        source: 'lmsd'
      },
      {
        zh: '谱梯度法的端点动力学与有限记忆收敛',
        en: 'Endpoint dynamics and finite-memory convergence',
        typeZh: '中文技术导读 · 6 页',
        typeEn: 'Technical reading note in Chinese · 6 pages',
        descriptionZh: '基于四篇公开合著预印本，推导平衡端点轨道、Lyapunov 能量和 Ritz 扫掠的行列式公式。',
        descriptionEn: 'A reading note based on four coauthored preprints, covering balanced endpoint orbits, Lyapunov energy, and the determinant identity for Ritz sweeps.',
        file: 'spectral-reading-note.pdf',
        source: 'spectral'
      }
    ];
    const disclosure = zh
      ? '阅读稿使用了 AI 辅助，仍待作者逐项核阅。引用研究结论时请引用原始预印本。'
      : 'The notes used AI assistance and are pending author review. Cite the original preprints for research results.';
    const items = notes.map(note => {
      const file = 'assets/documents/research/' + note.file;
      const source = 'https://github.com/Taitai2025/taitai2025.github.io/tree/main/research/' + note.source;
      return `<article class="paper paper--unnumbered"><div>
        <h3>${esc(zh ? note.zh : note.en)}</h3>
        <p class="paper-meta">2026.11 · ${esc(zh ? note.typeZh : note.typeEn)}</p>
        <p class="paper-summary">${esc(zh ? note.descriptionZh : note.descriptionEn)}</p>
        ${link(file, zh ? '阅读 PDF' : 'Read PDF')}
        ${link(file, zh ? '下载 PDF' : 'Download PDF', true)}
        ${link(source, zh ? '源文件与校验' : 'Source and checks')}
      </div></article>`;
    }).join('');
    const heading = zh ? '研究导读与复现' : 'Reading notes & reproducibility';
    return `<section id="research-reading" class="research-section">
      <h2>${heading}</h2><p class="source-note">${esc(disclosure)}</p>${items}
    </section>`;
  }
  function workingPapers(zh, notes, manuscripts) {
    if (!notes.length && !manuscripts.length) return '';
    const base = 'https://github.com/Taitai2025/taitai2025.github.io/tree/main/research';
    const repo = base + '/working';
    const byId = new Map(notes.map(note => [note.id, note]));
    const topics = [
      {id:'spectral', zh:'BB、LMSD 与 Ritz', en:'BB, LMSD, and Ritz values',
       groups:['BB 谱步长','LMSD 与 Ritz 重用','谱梯度与 Ritz','谱梯度与周期切换']},
      {id:'stepsizes', zh:'曲率信息、线搜索与停止', en:'Curvature information, line search, and stopping',
       groups:['曲率信息与步长','重启、投影与线搜索','步长设计与停止条件']},
      {id:'low-rank', zh:'低秩分解与 ADMM', en:'Low-rank decomposition and ADMM',
       groups:['低秩分解','ADMM 与参数选择']},
      {id:'design', zh:'最优实验设计', en:'Optimal experimental design', groups:['最优实验设计']}
    ];
    const heading = zh ? 'AI 辅助研究工作稿' : 'AI-assisted research working papers';
    const notice = zh
      ? '稿件经 AI 辅助整理，待作者人工核阅。全文整理版保留原证明和附录。各条目附 PDF、来源及可用的形式化或复现材料。'
      : 'These manuscripts used AI assistance and are pending author review. Archived full texts retain their original proofs and appendices. Each entry links to its PDF, sources, and available formalization or reproducibility files.';

    function card(paper, archived) {
      const pdf = 'assets/documents/research/' + paper.id + '.pdf';
      const title = esc(zh ? paper.zh : paper.en);
      const pages = zh ? paper.pages + ' 页' : paper.pages + ' pages';
      const meta = archived
        ? [zh ? '全文整理版' : 'Archived full text', zh ? '2026 年 11 月' : 'November 2026',
           pages + (zh ? '正文，加版本说明' : ' of manuscript, plus a cover note')]
        : [paper.releaseDate || '2026.11.25', 'v' + paper.version, pages];
      const manuscriptRepo = base + '/manuscripts';
      const source = archived
        ? paper.formal
          ? link(manuscriptRepo + '/' + paper.formal, zh ? '形式化与复现' : 'Formalization and checks')
          : link(manuscriptRepo, zh ? '版本与来源' : 'Versions and sources')
        : link(repo + '/' + paper.id, zh ? '源码与证据' : 'Source and evidence');
      const related = (paper.related || []).map(id => {
        const target = byId.get(id);
        if (!target) return '';
        return '<a class="document-link" href="#working-' + esc(id) + '">' +
          esc(zh ? target.zh : target.en) + '</a>';
      }).join('');
      const attachments = link(pdf, zh ? '论文 PDF' : 'Paper PDF') + source +
        (paper.arxiv ? link(paper.arxiv, zh ? '对应 arXiv 版本' : 'Related arXiv version') : '') +
        (paper.guide ? link('assets/documents/research/' + paper.guide, zh ? paper.guideZh : paper.guideEn) : '');
      const articleId = (archived ? 'manuscript-' : 'working-') + paper.id;
      const crossLinks = related
        ? '<p class="source-note">' + (zh ? '相关工作稿 ' : 'Related working papers ') + related + '</p>'
        : '';
      return '<article class="paper paper--unnumbered" id="' + esc(articleId) + '"><div>' +
        '<h4>' + title + '</h4><p class="paper-meta">' + meta.map(esc).join(' · ') + '</p>' +
        '<p class="paper-summary">' + esc(zh ? paper.descriptionZh : paper.descriptionEn) + '</p>' +
        attachments + crossLinks + '</div></article>';
    }

    const entries = manuscripts.map(paper => ({paper, archived:true}))
      .concat(notes.map(paper => ({paper, archived:false})));
    const section = (id, label, items) => items.length
      ? '<section class="research-work-group" aria-labelledby="research-topic-' + id + '">' +
        '<h3 id="research-topic-' + id + '">' + esc(label) + '</h3>' +
        items.map(({paper, archived}) => card(paper, archived)).join('') + '</section>'
      : '';
    const categorized = new Set(topics.flatMap(topic => topic.groups));
    const grouped = topics.map(topic => section(
      topic.id, zh ? topic.zh : topic.en, entries.filter(({paper}) => topic.groups.includes(paper.groupZh))
    )).join('');
    const additional = section('other', zh ? '其他研究' : 'Other research',
      entries.filter(({paper}) => !categorized.has(paper.groupZh)));
    return '<section id="research-working" class="research-section">' +
      (manuscripts.length ? '<span id="research-manuscripts" class="research-section-anchor" aria-hidden="true"></span>' : '') +
      '<h2>' + heading + '</h2><p class="source-note">' + esc(notice) + '</p><p>' +
      link(base, zh ? 'GitHub 研究资料' : 'Research files on GitHub') + '</p>' +
      grouped + additional + '</section>';
  }
  function render(lang){
    const zh=lang==='zh',data=window.RESEARCH_CONTENT;
    if(!data)return;
    const root=document.querySelector('#research .container');
    const papers=data.papers.map((p,i)=>'<article class="paper"><div class="paper-number">'+String(i+1).padStart(2,'0')+'</div><div><h3>'+esc(p.title)+'</h3><p class="paper-meta">'+esc(p.authors)+' · '+esc(p.date)+' · arXiv:'+esc(p.id)+'</p><p class="paper-meta">'+esc(zh?(p.venueZh||p.venue):p.venue)+'</p><p class="paper-summary">'+esc(zh?p.zh:p.en)+'</p>'+link('https://arxiv.org/abs/'+p.id,'arXiv')+attachments(p,zh)+'<details><summary>'+(zh?'引用信息':'Citation')+'</summary><p>'+esc(p.authors)+'. '+esc(p.title)+'. arXiv:'+esc(p.id)+' (2026).</p></details></div></article>').join('');
    root.innerHTML='<div class="research-heading">RESEARCH & WRITING · 2026</div><header class="research-top"><div><h1 class="research-title">'+(zh?'在谱结构与收敛之间':'Spectral structure.<br>Convergence theory.')+'</h1><p class="research-lead">'+(zh?'从 Barzilai–Borwein 方法到加权 LMSD，探索优化算法的动力学结构、收敛机制与最紧渐近速率。':'Exploring the dynamics, convergence mechanisms and sharp asymptotic rates of optimization algorithms, from Barzilai–Borwein methods to weighted LMSD.')+'</p><div class="research-topics"><span>Numerical optimization</span><span>Spectral gradient methods</span><span>Homogeneous dynamics</span></div></div><div class="research-count">04<small>ARXIV PREPRINTS</small></div></header><nav class="toc" aria-label="Research contents"><button data-scroll="research-papers">'+(zh?'01 预印本':'01 Preprints')+'</button><button data-scroll="research-articles">'+(zh?'02 发表文章':'02 Articles')+'</button><button data-scroll="research-talks">'+(zh?'03 学位论文与报告':'03 Thesis & talks')+'</button></nav><section id="research-papers" class="research-section"><h2><span class="section-number">01</span>'+(zh?'研究论文与预印本':'Research papers & preprints')+'</h2><p class="source-note">'+(zh?'以下四篇为与袁亚湘院士共同署名的 arXiv 预印本。各条目链接原始预印本及可获取的归档作者稿。以 arXiv 页面为准查看公开版本记录。':'These four arXiv preprints are coauthored with Academician Ya-xiang Yuan. The entries link to the original preprints and archived author manuscripts where available. See arXiv for the public version history.')+'</p>'+papers+'</section><section id="research-articles" class="research-section"><h2><span class="section-number">02</span>'+(zh?'发表文章与早期探索':'Articles & early explorations')+'</h2>'+list(data.articles,zh)+'</section><section id="research-talks" class="research-section"><h2><span class="section-number">03</span>'+(zh?'学位论文、报告与发言':'Thesis, reports & speeches')+'</h2>'+list(data.talks,zh)+'</section><footer class="site-footer">'+(zh?'欢迎交流数值优化、计算数学与相关问题。':'I welcome discussions on numerical optimization, computational mathematics and related topics.')+' <a href="mailto:yangshutai26@mails.ucas.ac.cn">yangshutai26@mails.ucas.ac.cn</a><br>2026.11.07 · Shutai Yang</footer>';
    const researchArticles=root.querySelector('#research-articles');
    if(researchArticles)researchArticles.insertAdjacentHTML('beforebegin',workingPapers(zh, data.working || [], data.manuscripts || [])+readingNote(zh));
    const nav=root.querySelector('nav.toc');
    if(nav){
      const button=document.createElement('button');
      button.dataset.scroll='research-reading';
      button.textContent=zh?'导读与复现':'Reading note & checks';
      nav.insertBefore(button,nav.children[1]||null);
      if (data.working?.length || data.manuscripts?.length) {
        const working = document.createElement('button');
        working.dataset.scroll = 'research-working';
        working.textContent = zh ? '工作稿' : 'Working papers';
        nav.insertBefore(working, button);
      }
    }
  }
  function decorateResume(){
    const container=document.querySelector('#resume .container');
    if(!container||container.querySelector('.resume-toc'))return;
    const sections=Array.from(container.querySelectorAll(':scope > .section'));
    const toc=document.createElement('nav');toc.className='toc resume-toc';toc.setAttribute('aria-label','履历目录 / Contents');
    sections.forEach((section,i)=>{const title=section.querySelector('h2');if(!title)return;section.id='resume-part-'+i;const button=document.createElement('button');button.dataset.scroll=section.id;button.textContent=title.textContent.replace(/📜|🎓|🎵/g,'').trim();toc.append(button);});
    const hero=container.querySelector('.resume-hero');if(hero)hero.after(toc);
  }
  document.addEventListener('click',e=>{const button=e.target.closest('[data-scroll]');if(button)document.getElementById(button.dataset.scroll)?.scrollIntoView({behavior:window.matchMedia('(prefers-reduced-motion: reduce)').matches?'auto':'smooth',block:'start'});});
  window.addEventListener('site:langchange',decorateResume);
  document.addEventListener('DOMContentLoaded',()=>{render(window.SiteLang?.getLang()||'zh');decorateResume();});
  window.Research={render};
})();
