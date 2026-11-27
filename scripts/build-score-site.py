#!/usr/bin/env python3
from html import escape
import json
from pathlib import Path
import re
from urllib.parse import urlparse
from xml.etree import ElementTree as ET

REPO = Path(__file__).resolve().parent.parent
SCORES = REPO / 'scores'
BASE = 'https://taitai2025.github.io'
TITLE = '国乐谱汇'
NAV = [
    ('/scores/', '首页'), ('/scores/library/', '专业谱库'), ('/scores/open/', '免费谱库'),
    ('/scores/arrangements/', '编配案例'), ('/scores/sources/', '总谱导航'),
    ('/scores/guides/', '排练指南'), ('/scores/tools/', '编制工具'),
]
GENERATED_PAGES = set()

def safe_url(value):
    if value.startswith('/scores/') and not value.startswith('//') and '..' not in value.split('/'):
        return value
    parsed = urlparse(value)
    if parsed.scheme == 'https' and parsed.netloc and not parsed.username and not parsed.password:
        return value
    raise ValueError(f'Unsupported link: {value}')

def anchor(url, label, classes=''):
    cls = f' class="{escape(classes)}"' if classes else ''
    return f'<a{cls} href="{escape(safe_url(url), quote=True)}">{escape(label)}</a>'

def badge(value, variant=''):
    return f'<span class="pill {variant}">{escape(value)}</span>'

def block(head, body):
    return f'<section class="shell"><div class="section-head"><h2>{escape(head)}</h2></div>{body}</section>'

def hero(eyebrow, title, copy, more='', sidebar=''):
    inner = f'<div><p class="eyebrow">{escape(eyebrow)}</p><h1>{escape(title)}</h1><p>{escape(copy)}</p>{more}</div>'
    cls = ' hero-layout' if sidebar else ''
    return f'<section class="hero"><div class="frame{cls}">{inner}{sidebar}</div></section>'

def head_links(active):
    links = ''.join(f'<a href="{path}"{" aria-current=page" if path == active else ""}>{label}</a>' for path,label in NAV)
    return f'<header class="site-header"><div class="frame"><a class="brand" href="/scores/">{TITLE}</a><nav class="nav" aria-label="主导航">{links}</nav></div></header>'

def output(route, title, desc, body, *, active='', script='', schema=None):
    assert route.startswith('/scores/') and route.endswith('/')
    GENERATED_PAGES.add(route)
    canonical = BASE + route
    js = f'<script src="{script}" defer></script>' if script else ''
    data = f'<script type="application/ld+json">{json.dumps(schema,ensure_ascii=False).replace("<",chr(92)+"u003c")}</script>' if schema else ''
    final_title=title+'｜'+TITLE
    metadata = f'<meta property="og:type" content="website"><meta property="og:site_name" content="{TITLE}"><meta property="og:title" content="{escape(final_title,quote=True)}"><meta property="og:description" content="{escape(desc,quote=True)}"><meta property="og:url" content="{canonical}">'
    html = f"""<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{escape(final_title)}</title>
<meta name="description" content="{escape(desc,quote=True)}"><link rel="canonical" href="{canonical}">{metadata}<link rel="stylesheet" href="/scores/style.css">{data}{js}</head>
<body><a class="skip" href="#main">跳到正文</a>{head_links(active or route)}<main id="main">{body}</main>
<footer class="site-footer"><div class="frame"><span>{TITLE} · 高校民乐团资源目录</span><nav class="actions" aria-label="页脚"><a href="/scores/tools/cooperation/">校谱反馈与共建</a><a href="/scores/archive/">既有口令资料</a><a href="/#resume">个人主页</a></nav></div></footer></body></html>
"""
    path = REPO / route.strip('/') / 'index.html'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(html,encoding='utf-8')

def card(title, copy, url, *, badges=(), meta='', attrs=''):
    shown = ''.join(badge(x) for x in badges)
    stat = f'<p class="meta">{escape(meta)}</p>' if meta else ''
    return f'<article class="card"{attrs}><div class="tags">{shown}</div><h3>{anchor(url,title)}</h3><p>{escape(copy)}</p>{stat}</article>'

def grid(cards):
    return '<div class="cards">'+''.join(cards)+'</div>'

def fields_search(scope_choices, ensembles=()):
    def select(label,name,items):
        return f'<label>{label}<select name="{name}"><option value="">全部</option>'+''.join(f'<option>{escape(x)}</option>' for x in sorted(set(items)))+'</select></label>'
    scopes = select('获取方式' if not ensembles else '谱件类别','scope',scope_choices)
    ensemble = select('编制','ensemble',ensembles) if ensembles else ''
    return f'<form hidden class="tools" data-filters><div class="filters"><label>搜索<input type="search" placeholder="曲名、作曲家、乐器或机构"></label>{scopes}{ensemble}</div><p class="filtered-count" data-filter-status role="status"></p></form>'

def filter_attr(search, scope='', ensemble=''):
    return f' data-entry data-search="{escape(search,quote=True)}" data-scope="{escape(scope,quote=True)}" data-ensemble="{escape(ensemble,quote=True)}"'

def filtered(cards, groups, ensembles=()):
    return '<section class="shell">'+fields_search(groups,ensembles)+grid(cards)+'<p hidden data-filter-empty class="callout">没有匹配条目。可以试试曲名简称或乐器名称。</p></section>'

def fact_list(pairs):
    return '<dl class="facts">'+''.join(f'<dt>{escape(k)}</dt><dd>{escape(v)}</dd>' for k,v in pairs if v)+'</dl>'

def get_details(w):
    return '/scores/work/'+w['slug']+'/'

def get_open(w):
    return '/scores/open/'+w['slug']+'/'

def file_section(w):
    cards=[]
    groups=[('combined','合订 PDF'),('parts','独立分谱'),('fullScores','简谱总谱')]
    for key,label in groups:
        links=[]
        for item in w[key]:
            measure = f'{item["pages"]:,} 页' if 'pages' in item else f'{item["count"]:,} 份 PDF'
            size=f'{item["bytes"]/1048576:.1f} MiB'
            links.append(f'<li>{anchor(item["url"], item["label"])} <small>{measure} · {size}</small></li>')
        text = '<ul>'+''.join(links)+'</ul>' if links else '<p class="muted">这一版本未登记独立总谱。</p>'
        cards.append(f'<article class="card"><h3>{label}</h3>{text}</article>')
    return grid(cards)

def work_card(w, filtering=True):
    search = ' '.join([w['title'],w['composer'],w['ensemble'],w['kind'],w['version'],*w['tags']])
    return card(w['title'],w['summary'],get_details(w),badges=(w['ensemble'],w['kind']),
        meta=f'{w["partCount"]} 份独立分谱 · {w["version"]}', attrs=filter_attr(search,w['kind'],w['ensemble']) if filtering else '')

def work_pages(works):
    for w in works:
        route=get_details(w)
        h=hero(w['ensemble'],w['title']+'简谱分谱',w['summary'],f'<div class="hero-actions">{anchor(route+"#files","查看文件","button primary")}{anchor("/scores/archive/#"+w["slug"],"按声部找分谱","button")}</div>')
        versions=[]
        parts=(SCORES/'parts-index.js').read_text(encoding='utf-8')
        variants=json.loads(parts.split('=',1)[1].strip().removesuffix(';')).get(w['slug'],[])
        names=' '.join(p['filename'] for p in variants)
        for term in ['首调','固定调','带主旋律','不带主旋律','A3']:
            flag = re.search(r'(?<![不无])带主旋律',names) if term=='带主旋律' else (term in names or term=='不带主旋律' and '无主旋律' in names)
            if flag: versions.append(term)
        detail=f'<section class="shell"><div class="cards two"><article class="card"><h2>谱件信息</h2>{fact_list([("曲目",w["title"]),("作曲与编曲",w["composer"]),("编制",w["ensemble"]),("现行版本",w["version"]),("乐章", "、".join(w.get("movements",[]))),("分谱",str(w["partCount"])+" 份"),("谱面", "、".join(versions))])}</article><article class="card"><h2>制谱与使用</h2>{fact_list([("文件核验",w["quality"]),("制谱权利",w["rights"]),("实际排练", "公开条目尚未登记试奏记录"),("修订说明",w["note"])])}<p class="meta">合订本与指挥总谱分别标注。下载后用已有口令打开 PDF。</p></article></div></section>'
        tagged=''.join(badge(tag,'neutral') for tag in w.get('instruments',[])[:18])
        roster=f'<section class="shell"><h2>声部索引</h2><div class="tags">{tagged}</div><p class="meta">按现有文件名登记。分章、兼奏和完整乐器列表见 {anchor("/scores/archive/#"+w["slug"],"分谱索引")}。</p></section>' if tagged else ''
        files=f'<section class="shell" id="files"><h2>乐谱版本与下载</h2>{file_section(w)}<p class="meta">ZIP 解压后，每份分谱 PDF 都有打开密码。演出、公开再发行和其他使用范围请按对应授权确认。</p></section>'
        feedback=f'<section class="shell"><div class="callout">有错音、错拍、换页或缺席声部问题时，可使用{anchor("/scores/tools/cooperation/","校谱反馈模板")}记录曲名、版次、小节和声部。</div></section>'
        desc=f'{w["title"]} {w["ensemble"]}。{w["partCount"]} 份独立简谱分谱、合订本及实际可取得的指挥总谱。查看谱面、版次、声部搜索和发布范围。'
        schema={'@context':'https://schema.org','@type':'WebPage','name':w['title']+'简谱分谱','url':BASE+route,'description':desc}
        output(route,w['title']+'简谱分谱 '+w['ensemble'],desc,h+detail+roster+files+feedback,active='/scores/library/',schema=schema)

def open_pages(opens):
    cards=[]
    for w in opens:
        route=get_open(w)
        card_copy=w['edition']
        search=' '.join([w['title'],w['composer'],w.get('composerEn',''),w['edition'],w['provider']])
        cards.append(card(w['title'],card_copy,route,badges=(w['rightsStatus'],w.get('format','五线谱总谱')),meta=f'{w["pages"]} 页 · {w["provider"]}',attrs=filter_attr(search,w['rightsStatus'])))
        music_format=w.get('format','五线谱总谱')
        desc=f'{w["title"]}，{w["composer"]}。{w["edition"]}。查看{music_format}的出处、许可和原谱下载。'
        links=f'<div class="hero-actions">{anchor(w["source"],"查看原版来源","button primary")}'
        if w['download'] != w['source']: links+=anchor(w['download'],'获取原站 PDF','button')
        links+='</div>'
        d=hero('免费谱库 · 原谱',w['title'],w['details'],links)
        d+=f'<section class="shell"><div class="cards two"><article class="card"><h2>版本与编制</h2>{fact_list([("作曲",w["composer"]),("版本",w["edition"]),("谱种",music_format),("来源",w["provider"]),("收录范围",str(w["pages"])+" 页")])}</article><article class="card"><h2>许可依据</h2><p>{escape(w["license"])}</p><p class="meta">按此谱本的标注及适用地区核对后使用。衍生谱、演出录音与现代改编需另看对应条款。</p>'
        if w.get('licenseUrl'): d+=anchor(w['licenseUrl'],'查看许可全文')
        d+='</article></div></section>'
        output(route,w['title']+' '+music_format,desc,d,active='/scores/open/')
    desc='从 IMSLP、Sibley 音乐图书馆和 Mutopia 等来源筛选公版或开放许可的古典总谱。逐谱提供版次、总谱下载与许可说明。'
    output('/scores/open/','免费总谱和开放乐谱',desc,hero('开放曲谱和公版来源','免费谱库','用于选曲、研究与配器的五线谱总谱与历史谱本。逐份登记版次、谱种和许可，并保留原站入口。')+filtered(cards,[w['rightsStatus'] for w in opens]),script='/scores/filters.js')

def source_page(sources):
    cards=[]
    for w in sources:
        provider=w.get('provider','')
        meta=' · '.join(str(x) for x in (provider,w.get('edition'),f'{w["pages"]} 页' if 'pages' in w else '') if x)
        desc=w.get('notes') or w.get('license') or '在原机构查看版本与使用条款。'
        title=w['title']
        search=' '.join([title,w.get('composer',''),provider,desc,str(w.get('category',''))])
        cards.append(card(title,desc,w['source'],badges=(w['access'],),meta=meta,attrs=filter_attr(search,w['access'])))
    intro=hero('官方谱源与出版入口','民族管弦乐总谱导航','从原机构下载、申请、租借或购买。按曲名、出版社、乐团及获取方式查找。')
    intro+='<section class="shell"><p class="callout">教育谱与活动限定谱，请查看谱本说明。编配、出版和再分发分别按相关授权处理。</p></section>'
    output('/scores/sources/','全球民族管弦乐总谱资源导航','收录香港中乐团、新加坡华乐团、台湾国乐团、吹鼓吹小站及出版商的官方谱源，覆盖下载、申请、购买与租借。',intro+filtered(cards,[w['access'] for w in sources]),script='/scores/filters.js')

def write_sitemap():
    path=REPO/'sitemap.xml'
    namespace='http://www.sitemaps.org/schemas/sitemap/0.9'
    ET.register_namespace('',namespace)
    tree=ET.parse(path)
    root=tree.getroot()
    for row in list(root):
        loc=row.findtext(f'{{{namespace}}}loc','')
        if loc.startswith(BASE+'/scores/'): root.remove(row)
    # Include authored static guides and helpers with canonical URLs and no noindex marker.
    for folder in ('guides','tools'):
        for file in sorted((SCORES/folder).rglob('index.html')):
            rel='/' + file.parent.relative_to(REPO).as_posix() + '/'
            expected=f'<link rel="canonical" href="{BASE}{rel}"'
            txt=file.read_text()
            if expected in txt and 'content="noindex' not in txt: GENERATED_PAGES.add(rel)
    for route in sorted(GENERATED_PAGES):
        url=ET.SubElement(root,f'{{{namespace}}}url')
        ET.SubElement(url,f'{{{namespace}}}loc').text=BASE+route
    ET.indent(tree,space='  ')
    tree.write(path,encoding='utf-8',xml_declaration=True)
    robots=(REPO/'robots.txt').read_text()
    assert 'Disallow: /scores' not in robots and f'Sitemap: {BASE}/sitemap.xml' in robots

def main():
    works=json.loads((SCORES/'data/works.json').read_text())
    source_data=json.loads((SCORES/'data/sources.json').read_text())
    opens=source_data['openScores']; sources=source_data['sources']
    all_slugs=[w['slug'] for w in [*works,*opens]]
    assert len(all_slugs)==len(set(all_slugs)) and all(re.fullmatch(r'[a-z0-9-]+', s) for s in all_slugs)
    assert all(w['rightsBasis'] and w['version'] and sum(x['count'] for x in w['parts'])==w['partCount'] for w in works)
    assert all(('公版' in w['license'] or w['license'].startswith(('CC BY ','CC BY-SA '))) and w['source'] and w['pages'] for w in opens)
    rosters={w['slug']:w for w in json.loads((SCORES/'tools/rosters.json').read_text())['works']}
    for w in works:
        observed=[label for r in rosters.get(w['slug'],{}).get('lines',[]) for label in [r['label'],*r['instruments']] if label]
        w['instruments']=list(dict.fromkeys(observed))
        w['tags']=list(dict.fromkeys(w['tags']+observed))
    summary={ 'works':[{k:w[k] for k in ('slug','title','composer','ensemble','tags','quality','rights','kind','partCount')} for w in works] }
    (SCORES/'data.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    sections = json.dumps([w['slug'] for w in works])
    (SCORES/'legacy-links.js').write_text('const scoreSlugs = '+sections+';\nconst oldSlug = location.hash.slice(1);\nif (scoreSlugs.includes(oldSlug)) location.replace("/scores/work/" + oldSlug + "/");\n')
    focus=[w for w in works if w['priority']<999]
    desc='高校民族乐团的简谱与总谱资源。查秦兵马俑、太阳颂、五声组曲等整曲合订本和固定调、首调独立分谱，查官方谱源及编制工具。'
    links='<div class="hero-actions">'+anchor('/scores/library/','查民乐简谱分谱','button primary')+anchor('/scores/sources/','找官方总谱','button')+'</div>'
    note=f'<aside class="hero-note"><h2>谱库收录</h2><p><strong>{len(works)} 个简谱版本</strong> · {sum(w["partCount"] for w in works):,} 份独立分谱</p><p>{len(opens)} 份开放总谱 · {len(sources)} 条原机构入口</p></aside>'
    search = '<form class="site-search" method="get" action="/scores/library/"><label for="home-q">搜索谱库</label><div><input id="home-q" name="q" type="search" maxlength="180" placeholder="曲名、作曲家或乐器"><button class="button primary" type="submit">搜曲谱</button></div></form>'
    home=hero('高校民族乐团乐谱资源','找谱、看编制、准备排练','查找民族管弦乐简谱、民乐与中西混编曲目。按曲目核对谱种、声部、版次和原谱来源。',search+links,note)
    home+=block('大型作品与分乐章套谱',grid([work_card(w,False) for w in focus])+f'<p class="actions">{anchor("/scores/library/","查看全部终版简谱","button")}</p>')
    home+=block('练团与制谱',grid([
        card('免费谱库','查看具体版次和许可，直接到原站获取公版及开放总谱。','/scores/open/'),
        card('编制与自适应编曲','检查现有编制的声部覆盖，或导入 MusicXML 试配。','/scores/tools/'),
        card('排练与校谱','从选曲、发谱、翻页到修订交接，使用可打印验收清单。','/scores/guides/'),
        card('民乐与中西混编','查看《大东北我的家乡》的三个编制和《La La Land》案例。','/scores/arrangements/'),
        card('高校共建','准备试奏反馈、校谱记录或原创编配合作草稿。','/scores/tools/cooperation/'),
    ]))
    output('/scores/','高校民乐简谱与民族管弦乐总谱',desc,home,script='/scores/legacy-links.js',schema={'@context':'https://schema.org','@type':'WebSite','name':TITLE,'url':BASE+'/scores/'})
    work_pages(works)
    open_pages(opens)
    source_page(sources)
    for key,title,copy,subset in [('/scores/library/','专业谱库','查找定版简谱，按曲名、乐器、编制或谱件类别筛选。',works),
                                 ('/scores/arrangements/','民乐与中西混编案例','按同一作品的不同编制比较谱件数量和交付形式。', [w for w in works if w['kind']=='编配版本'])]:
        output(key,title,copy+' 包含固定调和首调分谱、合订本及实际登记的指挥简谱总谱。',hero('曲目与版本',title,copy)+
            filtered([work_card(w) for w in subset],[w['kind'] for w in subset],[w['ensemble'] for w in subset]),script='/scores/filters.js')
    write_sitemap()
    print(f'{len(works)} protected works, {len(opens)} open editions, {len(sources)} catalogue entries, {len(GENERATED_PAGES)} indexable pages')
if __name__=='__main__':
    main()
