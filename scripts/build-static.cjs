/* Generate crawler-readable HTML from the same content used by the live site.
   Run after updating resume, research or notes: node scripts/build-static.cjs */
const fs = require('node:fs');
const path = require('node:path');
const { JSDOM } = require('jsdom');
const root = path.resolve(__dirname, '..');
const origin = 'https://taitai2025.github.io';
const read = relative => fs.readFileSync(path.join(root, relative), 'utf8');
const dom = new JSDOM('<div id="mount-resume"></div><div id="mount-research"></div><div id="mount-meditations"></div>', {url:origin+'/',runScripts:'outside-only'});
const w = dom.window;
for (const file of ['Content/EN/resume_EN.js','Content/ZH/resume_ZH.js','Content/EN/meditations_EN.js','Content/ZH/meditations_ZH.js','Content/research.js','Functions/Research.js']) w.eval(read('assets/js/'+file));
w.document.getElementById('resume').innerHTML = w.RESUME_ZH_INNER_HTML;
w.document.getElementById('meditations').innerHTML = w.MEDITATIONS_ZH_INNER_HTML;
w.Research.render('zh');
let html = read('index.html');
for (const name of ['resume','research','meditations']) {
  const opening = '<!-- static:'+name+':start -->';
  const closing = '<!-- static:'+name+':end -->';
  const mount = w.document.getElementById('mount-'+name);
  const content = opening+'\n'+mount.outerHTML+'\n'+closing;
  const pattern = new RegExp(opening+'[\\s\\S]*?'+closing);
  html = pattern.test(html) ? html.replace(pattern,()=>content) : html.replace('<div id="mount-'+name+'"></div>',content);
}
const description = '杨书泰（Shutai Yang）的个人主页：中国科学院大学计算数学直博生，培养单位中国科学院数学与系统科学研究院，导师袁亚湘院士。数值优化与谱梯度方法的论文、报告，以及民族音乐、笙演奏和乐团建设经历。';
const pages = [
  {dir:'',section:'cover',title:'杨书泰 Shutai Yang｜个人主页 · 计算数学与民族音乐',description},
  {dir:'about',section:'resume',title:'杨书泰 Shutai Yang｜个人简介、教育经历与荣誉',description},
  {dir:'research',section:'research',title:'杨书泰 Shutai Yang｜科研论文、预印本与学术报告',description:'杨书泰（Shutai Yang）的科研与写作：在袁亚湘院士指导下研究数值优化、Barzilai–Borwein 方法、加权 LMSD、收敛理论与最紧渐近速率。提供论文、arXiv 链接与报告 PDF。'},
  {dir:'notes',section:'meditations',title:'杨书泰 Shutai Yang｜随记、数学与音乐随笔',description:'杨书泰（Shutai Yang）的随记，记录数学学习、民族音乐、笙演奏、学生乐团建设与美育实践。'}
];
const person = {'@type':'Person','@id':origin+'/#person',name:'杨书泰',alternateName:['Shutai Yang','泰泰','Taitai','Thomas'],url:origin+'/about/',image:origin+'/assets/images/profile.jpg',jobTitle:'计算数学专业直博研究生',affiliation:[{'@type':'Organization',name:'中国科学院数学与系统科学研究院',url:'https://www.amss.ac.cn/'},{'@type':'CollegeOrUniversity',name:'中国科学院大学',url:'https://www.ucas.ac.cn/'}],alumniOf:{'@type':'CollegeOrUniversity',name:'中国科学技术大学'},sameAs:['https://orcid.org/0009-0003-5581-2970','https://github.com/Taitai2025'],knowsAbout:['Numerical optimization','Spectral gradient methods','Convergence theory','Sheng','Chinese orchestral music']};
for (const page of pages) {
  const canonical = origin+'/'+(page.dir?page.dir+'/':'');
  let output=html.replace(/<title>[\s\S]*?<\/title>/,'<title>'+page.title+'</title>')
    .replace(/<meta name="description"[^>]*>/,'<meta name="description" content="'+page.description+'">')
    .replace(/<meta name="keywords"[^>]*>\s*/,'')
    .replace(/<link rel="canonical"[^>]*>/,'<link rel="canonical" href="'+canonical+'">')
    .replace(/<meta property="og:title"[^>]*>/,'<meta property="og:title" content="'+page.title+'">')
    .replace(/<meta property="og:description"[^>]*>/,'<meta property="og:description" content="'+page.description+'">')
    .replace(/<meta property="og:url"[^>]*>/,'<meta property="og:url" content="'+canonical+'">')
    .replace(/<base[^>]*>\s*/,'')
    .replace(/<meta name="robots"[^>]*>\s*/,'')
    .replace(/<script id="site-structured-data"[\s\S]*?<\/script>\s*/,'')
    .replace(/<body[^>]*>/,'<body data-lang="zh" data-initial-page="'+page.section+'">');
  // Give each dedicated URL its own crawlable content; runtime mounts the other
  // sections as usual when the visitor navigates without reloading the page.
  if (page.dir) {
    for (const name of ['resume','research','meditations']) {
      if (name === page.section) continue;
      const start = '<!-- static:'+name+':start -->';
      const end = '<!-- static:'+name+':end -->';
      output = output.replace(new RegExp(start+'[\\s\\S]*?'+end),start+'\n<div id="mount-'+name+'"></div>\n'+end);
    }
  }
  const schema={'@context':'https://schema.org','@graph':[person,{'@type':page.section==='resume'||page.section==='cover'?'ProfilePage':'CollectionPage','@id':canonical+'#webpage',url:canonical,name:page.title,description:page.description,inLanguage:['zh-CN','en'],mainEntity:{'@id':origin+'/#person'},isPartOf:{'@id':origin+'/#website'}},{'@type':'WebSite','@id':origin+'/#website',url:origin+'/',name:'杨书泰 Shutai Yang 个人主页',publisher:{'@id':origin+'/#person'}}]};
  output=output.replace('<meta charset="UTF-8" />','<meta charset="UTF-8" />\n<base href="/">\n<meta name="robots" content="index, follow, max-image-preview:large">\n<script id="site-structured-data" type="application/ld+json">'+JSON.stringify(schema).replace(/</g,'\\u003c')+'</script>');
  const dest=page.dir?path.join(root,page.dir):root;
  fs.mkdirSync(dest,{recursive:true});fs.writeFileSync(path.join(dest,'index.html'),output.replace(/[\t ]+\r?$/gm,''));
}
fs.writeFileSync(path.join(root,'sitemap.xml'),'<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'+pages.map(p=>'  <url><loc>'+origin+'/'+(p.dir?p.dir+'/':'')+'</loc><lastmod>'+new Date().toISOString().slice(0,10)+'</lastmod></url>').join('\n')+'\n</urlset>\n');
console.log('Generated '+pages.length+' static entry pages from shared content.');
dom.window.close();
