(function () {
  'use strict';
  const mount=document.getElementById('mount-research');
  mount.innerHTML='<main id="research" aria-label="Research and writing"><div class="container"></div></main>';
  const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  function link(url,label,download=false){return '<a class="document-link" href="'+esc(url)+'" '+(download?'download':'target="_blank" rel="noopener noreferrer"')+'>'+esc(label)+(download?' ↓':' ↗')+'</a>';}
  function attachments(item,zh){return (item.file?link(item.file,zh?'PDF 阅读':'Read PDF')+link(item.file,zh?'下载':'Download',true):'')+(item.url?link(item.url,zh?'原文链接':'Source'):'');}
  function list(items,zh){return items.map((item,i)=>'<article class="paper"><div class="paper-number">'+String(i+1).padStart(2,'0')+'</div><div><h3>'+esc(item.title)+'</h3><p class="paper-meta">'+esc(item.meta)+'</p><p class="paper-summary">'+esc(zh?item.zh:item.en)+'</p>'+attachments(item,zh)+'</div></article>').join('');}
  function render(lang){
    const zh=lang==='zh',data=window.RESEARCH_CONTENT;
    if(!data)return;
    const root=document.querySelector('#research .container');
    const papers=data.papers.map((p,i)=>'<article class="paper"><div class="paper-number">'+String(i+1).padStart(2,'0')+'</div><div><h3>'+esc(p.title)+'</h3><p class="paper-meta">'+esc(p.authors)+' · '+esc(p.date)+' · arXiv:'+esc(p.id)+'</p><p class="paper-meta">'+esc(zh?(p.venueZh||p.venue):p.venue)+'</p><p class="paper-summary">'+esc(zh?p.zh:p.en)+'</p>'+link('https://arxiv.org/abs/'+p.id,'arXiv')+attachments(p,zh)+'<details><summary>'+(zh?'引用信息':'Citation')+'</summary><p>'+esc(p.authors)+'. '+esc(p.title)+'. arXiv:'+esc(p.id)+' (2026).</p></details></div></article>').join('');
    root.innerHTML='<div class="research-heading">RESEARCH & WRITING · 2026</div><header class="research-top"><div><h1 class="research-title">'+(zh?'在谱结构与收敛之间':'Spectral structure.<br>Convergence theory.')+'</h1><p class="research-lead">'+(zh?'从 Barzilai–Borwein 方法到加权 LMSD，探索优化算法的动力学结构、收敛机制与最紧渐近速率。':'Exploring the dynamics, convergence mechanisms and sharp asymptotic rates of optimization algorithms, from Barzilai–Borwein methods to weighted LMSD.')+'</p><div class="research-topics"><span>Numerical optimization</span><span>Spectral gradient methods</span><span>Homogeneous dynamics</span></div></div><div class="research-count">04<small>ARXIV PREPRINTS</small></div></header><nav class="toc" aria-label="Research contents"><button data-scroll="research-papers">'+(zh?'01 预印本':'01 Preprints')+'</button><button data-scroll="research-articles">'+(zh?'02 发表文章':'02 Articles')+'</button><button data-scroll="research-talks">'+(zh?'03 报告与发言':'03 Talks & speech')+'</button></nav><section id="research-papers" class="research-section"><h2><span class="section-number">01</span>'+(zh?'研究论文与预印本':'Research papers & preprints')+'</h2><p class="source-note">'+(zh?'四篇论文均在研究生导师袁亚湘老师的指导下完成，并与导师共同署名。目前三篇在投，一篇为预印本；在投不代表已接收。本站 PDF 为公开 arXiv v1 版本；arXiv 链接指向版本记录，可查看后续修订。':'All four papers were completed under the guidance of my doctoral advisor, Ya-xiang Yuan, and are coauthored with him. Three manuscripts are under review and one is a preprint; submission does not imply acceptance. Local PDFs are public arXiv v1 copies; see arXiv for version history and subsequent revisions.')+'</p>'+papers+'</section><section id="research-articles" class="research-section"><h2><span class="section-number">02</span>'+(zh?'发表文章与早期探索':'Articles & early explorations')+'</h2>'+list(data.articles,zh)+'</section><section id="research-talks" class="research-section"><h2><span class="section-number">03</span>'+(zh?'报告、讲义与发言':'Talks, notes & speech')+'</h2>'+list(data.talks,zh)+'</section><footer class="site-footer">'+(zh?'欢迎交流数值优化、计算数学与相关问题。':'I welcome discussions on numerical optimization, computational mathematics and related topics.')+' <a href="mailto:yangshutai26@mails.ucas.ac.cn">yangshutai26@mails.ucas.ac.cn</a><br>2026.10.23 · Shutai Yang</footer>';
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
