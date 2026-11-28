#!/usr/bin/env python3
from html import escape
import json
from pathlib import Path
import re
import sys
from urllib.parse import urlencode, urlparse
from xml.etree import ElementTree as ET

REPO = Path(__file__).resolve().parent.parent
SCORES = REPO / 'scores'
sys.path.insert(0, str(SCORES / 'tools'))
sys.dont_write_bytecode = True
from build_rosters import ALIASES, observed_label, window_json
import score_community

BASE = 'https://taitai2025.github.io'
TITLE = '国乐谱汇'
NAV = [
    ('/scores/', '首页'), ('/scores/library/', '专业谱库'), ('/scores/open/', '免费谱库'),
    ('/scores/arrangements/', '编配案例'), ('/scores/sources/', '总谱导航'),
    ('/scores/guides/', '排练指南'), ('/scores/tools/', '编制工具'),
    ('/scores/orchestras/', '乐团风采'),
]
GENERATED_PAGES = set()
SEARCH_ALIASES = ('高笙', '中笙', '低笙', '高唢', '中唢', '次中音唢', '低唢', '低革胡', '筝', '贝司', '吊钹')
INSTRUMENT_GROUPS = {
    '笛子': ('梆笛', '曲笛', '新笛'),
    '竹笛': ('梆笛', '曲笛', '新笛'),
    '民族吹管': ('梆笛', '曲笛', '新笛', '箫', '埙', '高音笙', '中音笙', '低音笙', '高音唢呐', '中音唢呐', '次中音唢呐', '低音唢呐'),
    '弹拨乐': ('柳琴', '琵琶', '中阮', '大阮', '三弦', '古筝', '古琴', '扬琴'),
    '拉弦乐': ('高胡', '二胡', '中胡', '革胡', '低音革胡', '胡琴'),
}

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
    brand = f'<a class="brand" href="/scores/"><span class="brand-seal" aria-hidden="true">谱</span><span>{TITLE}</span></a>'
    planner = '<a class="header-action" href="/scores/planner/">我的选曲单</a>'
    return f'<header class="site-header"><div class="frame">{brand}<nav class="nav" aria-label="主导航">{links}</nav>{planner}</div></header>'

def output(route, title, desc, body, *, active='', script='', extra_script='', schema=None, index=True):
    assert route.startswith('/scores/') and route.endswith('/')
    if index:
        GENERATED_PAGES.add(route)
    canonical = BASE + route
    js = ''.join(f'<script src="{path}" defer></script>' for path in (script, extra_script) if path)
    robots = '' if index else '<meta name="robots" content="noindex, follow">'
    data = f'<script type="application/ld+json">{json.dumps(schema,ensure_ascii=False).replace("<",chr(92)+"u003c")}</script>' if schema else ''
    final_title=title+'｜'+TITLE
    metadata = f'<meta property="og:type" content="website"><meta property="og:site_name" content="{TITLE}"><meta property="og:title" content="{escape(final_title,quote=True)}"><meta property="og:description" content="{escape(desc,quote=True)}"><meta property="og:url" content="{canonical}">'
    html = f"""<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{escape(final_title)}</title>
<meta name="description" content="{escape(desc,quote=True)}"><link rel="canonical" href="{canonical}">{metadata}{robots}<link rel="icon" href="/scores/mark.svg" type="image/svg+xml"><link rel="stylesheet" href="/scores/style.css"><link rel="stylesheet" href="/scores/experience.css"><link rel="stylesheet" href="{score_community.asset_url('community.css')}">{data}{js}<script src="/scores/experience.js" defer></script></head>
<body><a class="skip" href="#main">跳到正文</a>{head_links(active or route)}<main id="main">{body}</main>
<footer class="site-footer"><div class="frame"><span>{TITLE} · 高校民乐团资源目录</span><nav class="actions" aria-label="页脚"><a href="/scores/about/">使用说明</a><a href="/scores/contact/">联系与查阅</a><a href="/scores/orchestras/submit/">乐团投稿</a><a href="/scores/updates/">版本动态</a><a href="/scores/support/">支持本站</a><a href="/#resume">个人主页</a></nav></div></footer></body></html>
"""
    path = REPO / route.strip('/') / 'index.html'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(html,encoding='utf-8')

def card(title, copy, url, *, badges=(), meta='', attrs='', extra=''):
    shown = ''.join(badge(x) for x in badges)
    stat = f'<p class="meta">{escape(meta)}</p>' if meta else ''
    return f'<article class="card"{attrs}><div class="tags">{shown}</div><h3>{anchor(url,title)}</h3><p>{escape(copy)}</p>{stat}{extra}</article>'

def grid(cards):
    return '<div class="cards">'+''.join(cards)+'</div>'

def fields_search(scope_choices, ensembles=(), scope_label='', extra_filters=()):
    def select(label,name,items):
        return f'<label>{escape(label)}<select name="{name}" data-filter-key="{name}"><option value="">全部</option>'+''.join(f'<option>{escape(x)}</option>' for x in sorted(set(items)))+'</select></label>'
    scopes = select(scope_label or ('获取方式' if not ensembles else '谱件类别'),'scope',scope_choices) if scope_choices else ''
    ensemble = select('编制','ensemble',ensembles) if ensembles else ''
    extras = ''.join(select(label,name,items) for name,label,items in extra_filters if items)
    return f'<form hidden class="tools" data-filters><div class="filters"><label>搜索<input type="search" maxlength="180" placeholder="曲名、作曲家、乐器或机构"></label>{scopes}{ensemble}{extras}</div><div class="filter-summary"><p class="filtered-count" data-filter-status role="status"></p><button type="reset" class="button">清除筛选</button></div></form>'

def filter_attr(search, scope='', ensemble='', *, title='', formats=(), facets=None):
    title_attr = f' data-work-title="{escape(title,quote=True)}"' if title else ''
    format_attr = f' data-formats="{escape("|".join(formats),quote=True)}"' if formats else ''
    facet_attrs = ''.join(f' data-{key}="{escape("|".join(values),quote=True)}"' for key,values in (facets or {}).items())
    return f' data-entry data-search="{escape(search,quote=True)}" data-scope="{escape(scope,quote=True)}" data-ensemble="{escape(ensemble,quote=True)}"{title_attr}{format_attr}{facet_attrs}'

def filtered(cards, groups, ensembles=(), scope_label='', extra_filters=()):
    return '<section class="shell">'+fields_search(groups,ensembles,scope_label,extra_filters)+grid(cards)+'<p hidden data-filter-empty class="callout">没有匹配条目。可减少筛选条件，或试试曲名简称、乐器名称。</p></section>'

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
        empty = {'combined': '这一版本未登记合订本。', 'parts': '这一版本未登记独立分谱包。', 'fullScores': '这一版本未登记独立指挥总谱。'}
        text = '<ul>'+''.join(links)+'</ul>' if links else f'<p class="muted">{empty[key]}</p>'
        cards.append(f'<article class="card"><h3>{label}</h3>{text}</article>')
    return grid(cards)

def work_card(w, filtering=True, group=''):
    search = ' '.join([w['title'],w['composer'],w['ensemble'],w['kind'],w['version'],*w['tags'],*w.get('movements',[])])
    formats = ['简谱', '分谱', '简谱分谱', *w['variants']]
    if w['combined']:
        formats.append('合订本')
    if w['fullScores']:
        formats.extend(('总谱', '简谱总谱', '指挥总谱', '简谱指挥总谱'))
    attrs=filter_attr(search,group or w['kind'],w['ensemble'],title=w['title'],formats=formats,facets={'format': formats})
    badges = [w['ensemble'], w['kind'], '简谱分谱']
    if w['fullScores']:
        badges.append('简谱指挥总谱')
    return card(w['title'],w['summary'],get_details(w),badges=badges,
        meta=f'{w["partCount"]} 份独立分谱 · {w["version"]}', attrs=attrs if filtering else '')

def instrument_terms(names):
    return list(dict.fromkeys([
        *names, *(alias for alias in SEARCH_ALIASES if ALIASES[alias] in names),
        *(group for group,members in INSTRUMENT_GROUPS.items() if any(name in members for name in names)),
    ]))

def melody_variants(parts, *, infer_pairs):
    names = {item['filename'] for item in parts}
    marker = re.compile(r'_带主旋律(?=[_｜.]|$)')
    inferred_without = set()
    if infer_pairs:
        for name in names:
            if len(marker.findall(name)) == 1 and '主旋律备用' not in name:
                candidate = marker.sub('', name)
                if candidate in names and '主旋律' not in candidate:
                    inferred_without.add(candidate)
    variants = {}
    for name in names:
        if re.search(r'(?:_|｜|^)主旋律备用(?=[_｜.]|$)', name):
            variants[name] = 'reserve'
        elif re.search(r'(?:_|｜|^)(?:不带|无)主旋律(?:提示)?(?=[_｜.]|$)', name) or name in inferred_without:
            variants[name] = 'without'
        elif re.search(r'(?:_|｜|^)带主旋律(?:提示)?(?=[_｜.]|$)', name):
            variants[name] = 'with'
        else:
            variants[name] = 'unknown'
    return variants

def part_formats(melody):
    formats = [term for term in ('首调', '固定调') if any(term in name for name in melody)]
    states = set(melody.values())
    if 'with' in states:
        formats.append('带主旋律')
    if 'without' in states:
        formats.append('不带主旋律')
    if any('A3' in name for name in melody):
        formats.append('A3')
    return formats

def voice_section(w, variants):
    grouped={}
    for item in variants:
        grouped.setdefault(observed_label(item['filename']), []).append(item)
    if not grouped:
        return ''
    lines=[]
    for entry in w['roster']:
        label=entry['label']
        files=grouped.pop(label,[])
        if not files:
            continue
        lookup=' '.join([label,*instrument_terms(entry['instruments'])])
        optional=' · 可选' if entry['kind']=='optional' else ' · 备用' if entry['kind']=='reserve' else ''
        items=''.join(
            f'<li data-filename="{escape(p["filename"],quote=True)}" data-melody="{w["melody"][p["filename"]]}" '
            f'data-part-pages="{p["pages"]}">{escape(p["filename"])} <small>· {p["pages"]} 页</small></li>'
            for p in files
        )
        lines.append(f'<details class="voice-list"{filter_attr(lookup)}><summary>{escape(label)} <small><span data-voice-count>{len(files)}</span> 份{optional}</small></summary><ul>{items}</ul></details>')
    assert not grouped, f'Rebuild scores/tools/rosters.json for {w["slug"]}'
    search='<form hidden class="tools" data-filters><label class="field">筛选文件<input type="search" maxlength="180" placeholder="如高音笙 首调，多个关键词用空格分开"></label><p class="filtered-count" data-filter-status role="status"></p></form>'
    links=anchor('/scores/instruments/','全库乐器索引')+' · '+anchor(get_details(w)+'#files','下载本曲全集')
    release_tags=escape(' '.join(dict.fromkeys(urlparse(p['url']).path.split('/')[-2] for p in w['parts'])),quote=True)
    preview='''<template data-part-pdf-preview>
<dialog class="part-pdf-dialog" aria-labelledby="part-pdf-title" aria-describedby="part-pdf-status">
<div class="dialog-heading"><h2 id="part-pdf-title">分谱 PDF</h2><form method="dialog"><button class="button">关闭</button></form></div>
<p id="part-pdf-status" class="meta" role="status">正在读取 PDF…</p>
<div class="actions"><a class="button" data-part-pdf-download>下载此 PDF</a><a class="button" data-part-pdf-new-tab target="_blank" rel="noopener" hidden>在新标签页打开</a></div>
<iframe title="分谱 PDF 预览" hidden></iframe>
</dialog>
</template>'''
    return f'<section class="shell" id="voices" data-part-work="{escape(w["slug"],quote=True)}" data-part-tags="{release_tags}"><h2>分谱文件索引</h2><p class="meta">展开声部可核对文件名和实际页数。已发布单件链接的分谱可直接打开 PDF。兼奏、备用和不同谱式分别显示，PDF 使用该版本原有口令。</p>{search}<div class="voice-index">{"".join(lines)}</div><p hidden data-filter-empty class="callout">没有匹配文件。试试乐器原名、简谱版本或乐章。</p><p class="actions">{links}</p>{preview}</section>'

def instruments_page(works, families):
    library={}
    for work in works:
        canonicals={name for line in work['roster'] for name in line['instruments']}
        for name in canonicals:
            library.setdefault(name,[]).append(work)
    cards=[]
    categories={}
    for family,names in families.items():
        for name in names:
            group=library.get(name)
            if not group or name in categories:
                continue
            categories[name]=family
            rows=[]
            for w in group:
                url=get_details(w)+'?'+urlencode({'q':name})+'#voices'
                rows.append('<li>'+anchor(url,w['title'])+'</li>')
            lookup=' '.join([*instrument_terms([name]),family,*(w['title'] for w in group)])
            cards.append(f'<article class="card"{filter_attr(lookup,family)}><h3>{escape(name)}</h3><p class="meta">{escape(family)} · {len(group)} 个曲目版本</p><ul class="compact-list">{"".join(rows)}</ul></article>')
    assert set(categories)==set(library)
    desc='按曲笛、高音笙、唢呐、琵琶、二胡、中阮等乐器查找国乐谱汇的简谱分谱、谱式和 ZIP 内文件页数。'
    intro=hero('专业谱库','按乐器找简谱分谱','按乐器找到曲目，再核对具体乐章、固定调或首调、主旋律提示和页数。这里列出已发布文件中的乐器。')
    output('/scores/instruments/','按乐器找简谱分谱',desc,intro+filtered(cards,categories.values(),scope_label='乐器类别'),active='/scores/library/',script='/scores/filters.js')

def work_pages(works, parts):
    for w in works:
        route=get_details(w)
        h=hero(w['ensemble'],w['title']+'简谱分谱',w['summary'],f'<div class="hero-actions">{anchor(route+"#files","查看文件","button primary")}{anchor(route+"#voices","按声部找分谱","button")}</div>')
        variants=parts.get(w['slug'],[])
        versions=w['variants']
        detail=f'<section class="shell"><div class="cards two"><article class="card"><h2>谱件信息</h2>{fact_list([("曲目",w["title"]),("作曲与编曲",w["composer"] or "署名待补录"),("编制",w["ensemble"]),("现行版本",w["version"]),("乐章", "、".join(w.get("movements",[]))),("分谱",str(w["partCount"])+" 份"),("谱面", "、".join(versions))])}<p class="meta">分谱数量包含不同乐章、谱式和提示版本，不代表声部或演奏员人数。</p></article><article class="card"><h2>制谱与使用</h2>{fact_list([("文件核验",w["quality"]),("内容校勘",w.get("contentReview","验收记录待整理")),("制谱权利",w["rights"]),("实际排练", w.get("rehearsal","尚未登记试奏记录")),("修订说明",w["note"])])}<p class="meta">保留原交付版本名称；文件核验、内容校勘与实际试奏分别记录。</p></article></div></section>'
        roster=voice_section(w,variants)
        files=f'<section class="shell" id="files"><h2>乐谱版本与下载</h2>{file_section(w)}<p class="meta">ZIP 解压后，每份分谱 PDF 都有打开密码。演出、公开再发行和其他使用范围请按对应授权确认。</p></section>'
        feedback=f'<section class="shell"><div class="callout">有错音、错拍、换页或缺席声部问题时，可使用{anchor("/scores/tools/cooperation/","校谱反馈模板")}记录曲名、版次、小节和声部。</div></section>'
        assets='独立简谱分谱与合订本'+('，另附简谱指挥总谱' if w['fullScores'] else '')
        desc=f'{w["title"]} {w["ensemble"]}。{w["partCount"]} 份{assets}。查看谱面、版次、声部搜索和发布范围。'
        schema={'@context':'https://schema.org','@type':'WebPage','name':w['title']+'简谱分谱','url':BASE+route,'description':desc}
        output(route,w['title']+'简谱分谱 '+w['ensemble'],desc,h+score_community.access_notice(w['title'],w['version'])+detail+files+roster+feedback,active='/scores/library/',script='/scores/filters.js',extra_script='/scores/part-pdf.js',schema=schema)

def open_metadata(w):
    music_format=w.get('format','五线谱总谱')
    formats=[music_format]
    formats.extend(term for term in ('五线谱', '简谱', '分谱', '总谱', '工尺谱', '减字谱', '缩谱') if term in music_format)
    if music_format.startswith('古琴减字谱'):
        formats.extend(('古琴谱', '古琴减字谱'))
    notations=[name for marker,name in [('五线谱','五线谱'),('简谱','简谱'),('工尺','工尺谱'),('减字谱','古琴减字谱')] if marker in music_format]
    return {'formats': list(dict.fromkeys(formats)), 'notations': notations, 'instruments': w.get('instruments',[])}

def open_card(w, group=''):
    music_format=w.get('format','五线谱总谱')
    meta=open_metadata(w)
    search=' '.join([w['title'],w['composer'],w.get('composerEn',''),w['edition'],w['provider'],w['rightsStatus'],w['license'],*meta['formats'],*instrument_terms(meta['instruments'])])
    return card(w['title'],w['edition'],get_open(w),badges=(w['rightsStatus'],music_format),
                meta=f'{w["pages"]} 页 · {w["provider"]}',attrs=filter_attr(search,group or w['rightsStatus'],title=w['title'],formats=meta['formats'],facets={'notation':meta['notations'],'instrument':meta['instruments']}))

def open_download_label(w):
    kind=w.get('downloadType','')
    path=urlparse(w['download']).path.lower()
    if kind=='zip' or path.endswith('.zip'):
        return '下载总分谱 ZIP'
    if kind=='pdf' or path.endswith('.pdf'):
        return '获取原站 PDF'
    return '获取原站文件'

def open_pages(opens):
    for w in opens:
        route=get_open(w)
        music_format=w.get('format','五线谱总谱')
        desc=f'{w["title"]}，{w["composer"]}。{w["edition"]}。查看{music_format}的出处、许可和原谱下载。'
        links=f'<div class="hero-actions">{anchor(w["source"],"查看原版来源","button primary")}'
        volumes=w.get('volumes',[])
        if volumes:
            links+=anchor(route+'#volumes','查看各卷下载','button')
        elif w['download'] != w['source']:
            links+=anchor(w['download'],open_download_label(w),'button')
        links+='</div>'
        d=hero('免费谱库 · 原谱',w['title'],w['details'],links)
        d+=f'<section class="shell"><div class="cards two"><article class="card"><h2>版本与编制</h2>{fact_list([("作曲",w["composer"] or "署名待补录"),("版本",w["edition"]),("谱种",music_format),("编制与乐器","、".join(w.get("instruments",[]))),("来源",w["provider"]),("收录范围",str(w["pages"])+" 页")])}</article><article class="card"><h2>许可依据</h2><p>{escape(w["license"])}</p><p class="meta">按此谱本的标注及适用地区核对后使用。衍生谱、演出录音与现代改编需另看对应条款。</p>'
        if w.get('licenseUrl'): d+=anchor(w['licenseUrl'],'查看公版或许可说明')
        d+='</article></div></section>'
        if volumes:
            rows=[]
            for volume in volumes:
                start,end=volume['scanPages']
                rows.append(f'<li>{anchor(volume["download"],volume["label"]+" · 原册 PDF")} <small>第 {start}–{end} 页</small></li>')
            d+=f'<section class="shell" id="volumes"><h2>各卷原谱</h2><p>按各册的 PDF 页序查找本曲。</p><ul>{"".join(rows)}</ul></section>'
        output(route,w['title']+' '+music_format,desc,d,active='/scores/open/')
    desc='筛选公版或开放许可的古典总谱与历史谱本，逐谱提供版次、原谱出处、下载与许可说明。'
    extra_filters=[('notation','记谱方式',[n for w in opens for n in open_metadata(w)['notations']]),('instrument','编制与乐器',[n for w in opens for n in w.get('instruments',[])])]
    output('/scores/open/','免费总谱和开放乐谱',desc,hero('开放曲谱和公版来源','免费谱库','用于选曲、研究与配器的原版谱本。先按记谱方式和乐器筛选，再核对版次、许可与原站下载。')+filtered([open_card(w) for w in opens],[w['rightsStatus'] for w in opens],scope_label='许可',extra_filters=extra_filters),script='/scores/filters.js')

def source_card(w, group=''):
    provider=w.get('provider','')
    meta=' · '.join(str(x) for x in (w.get('composer'),provider,w.get('edition'),f'{w["pages"]} 页' if 'pages' in w else '') if x)
    desc=w.get('notes') or w.get('license') or '在原机构查看版本与使用条款。'
    title=w['title']
    category=w.get('category','')
    search=' '.join([title,w.get('composer',''),provider,desc,category,w.get('edition',''),w['access'],w.get('accessDetail','')])
    score_evidence=' '.join([title,category,w.get('details',''),desc])
    formats=[]
    if re.search(r'总[分谱]',score_evidence):
        formats.append('总谱')
    if re.search(r'分谱|总分谱',score_evidence):
        formats.append('分谱')
    version_links = ''
    if w.get('scoreVersions'):
        rows = ''.join(f'<li>{anchor(version["source"],version["label"]+" · PDF")}<small>文件 {version["pages"]} 页 · 总谱正文第 {escape(version["scorePages"])} 页</small></li>' for version in w['scoreVersions'])
        version_links = f'<details class="source-versions"><summary>展开 {len(w["scoreVersions"])} 个官方总谱版本</summary><ul class="source-version-list">{rows}</ul><p class="meta">原站核对：<time datetime="{escape(w["checkedAt"])}">{escape(w["checkedAt"])}</time>。分谱申请与使用条件请查看上方原机构页面。</p></details>'
    return card(title,desc,w['source'],badges=(w['access'],),meta=meta,extra=version_links,attrs=filter_attr(search,group or w['access'],title=title,formats=formats,facets={'provider':[provider or '综合资源']}))

def source_page(sources):
    intro=hero('官方谱源与出版入口','民族管弦乐总谱导航','从原机构下载、申请、租借或购买。按曲名、出版社、乐团及获取方式查找。')
    intro+='<section class="shell"><p class="callout">教育谱与活动限定谱，请查看谱本说明。编配、出版和再分发分别按相关授权处理。</p></section>'
    output('/scores/sources/','全球民族管弦乐总谱资源导航','收录香港中乐团、新加坡华乐团、台湾国乐团、吹鼓吹小站及出版商的官方谱源，覆盖下载、申请、购买与租借。',intro+filtered([source_card(w) for w in sources],[w['access'] for w in sources],extra_filters=[('provider','来源机构',[w.get('provider') or '综合资源' for w in sources])]),script='/scores/filters.js')

def search_page(works, opens, sources):
    groups=('已发布简谱','开放谱本','官方及出版谱源')
    cards=[*(work_card(w,group=groups[0]) for w in works),*(open_card(w,group=groups[1]) for w in opens),*(source_card(w,group=groups[2]) for w in sources)]
    desc='同时查找曲名、乐器和出版谱源，再按资源类型筛选搜索结果。'
    intro=hero(TITLE,'搜索谱库',desc)
    output('/scores/search/','搜索谱库',desc,intro+filtered(cards,groups,scope_label='资源类型'),script='/scores/filters.js',index=False)

def write_sitemap():
    namespace='http://www.sitemaps.org/schemas/sitemap/0.9'
    ET.register_namespace('',namespace)
    root=ET.parse(REPO/'sitemap.xml').getroot()
    for row in list(root):
        loc=row.findtext(f'{{{namespace}}}loc','')
        if loc.startswith(BASE+'/scores/'): root.remove(row)
    # Include authored static guides and helpers with canonical URLs and no noindex marker.
    for folder in ('guides','tools','orchestras'):
        for file in sorted((SCORES/folder).rglob('index.html')):
            rel='/' + file.parent.relative_to(REPO).as_posix() + '/'
            expected=f'<link rel="canonical" href="{BASE}{rel}"'
            txt=file.read_text()
            if expected in txt and 'content="noindex' not in txt: GENERATED_PAGES.add(rel)
    score_root=ET.Element(f'{{{namespace}}}urlset')
    for sitemap,sitemap_path in ((root,REPO/'sitemap.xml'),(score_root,SCORES/'sitemap.xml')):
        for route in sorted(GENERATED_PAGES):
            url=ET.SubElement(sitemap,f'{{{namespace}}}url')
            ET.SubElement(url,f'{{{namespace}}}loc').text=BASE+route
        ET.indent(sitemap,space='  ')
        ET.ElementTree(sitemap).write(sitemap_path,encoding='utf-8',xml_declaration=True)
    robots=(REPO/'robots.txt').read_text()
    assert 'Disallow: /scores' not in robots
    assert all(f'Sitemap: {BASE}{route}' in robots.splitlines() for route in ('/sitemap.xml','/scores/sitemap.xml'))

def prepare_works(works, roster_data, parts):
    """Derive public search metadata from the same observed file and roster index."""
    rosters={w['slug']:w for w in roster_data['works']}
    family_by_instrument={}
    for family,names in roster_data['families'].items():
        for name in names:
            family_by_instrument.setdefault(name,family)
    for w in works:
        w['roster']=rosters[w['slug']]['lines']
        assert len(parts[w['slug']])==w['partCount']
        # The filename index lacks per-ZIP attribution for works with several downloads.
        w['melody']=melody_variants(parts[w['slug']], infer_pairs=len(w['parts']) == 1)
        w['variants']=part_formats(w['melody'])
        observed=[label for r in w['roster'] for label in [r['label'],*instrument_terms(r['instruments'])] if label]
        families=[family_by_instrument[name] for r in w['roster'] for name in r['instruments'] if name in family_by_instrument]
        w['tags']=list(dict.fromkeys(w['tags']+observed+families+w.get('movements',[])))
    return works

def main():
    works=json.loads((SCORES/'data/works.json').read_text())
    source_data=json.loads((SCORES/'data/sources.json').read_text())
    opens=source_data['openScores']; sources=source_data['sources']
    all_slugs=[w['slug'] for w in [*works,*opens]]
    assert len(all_slugs)==len(set(all_slugs)) and all(re.fullmatch(r'[a-z0-9-]+', s) for s in all_slugs)
    assert all(w['rightsBasis'] and w['version'] and sum(x['count'] for x in w['parts'])==w['partCount'] for w in works)
    assert all(('公版' in w['license'] or w['license'].startswith(('CC BY ','CC BY-SA '))) and w['source'] and w['pages'] for w in opens)
    roster_data=json.loads((SCORES/'tools/rosters.json').read_text())
    parts=window_json(SCORES/'parts-index.js')
    prepare_works(works,roster_data,parts)
    summary={ 'works':[{k:w[k] for k in ('slug','title','composer','ensemble','tags','variants','quality','rights','kind','partCount')} for w in works] }
    (SCORES/'data.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    sections = json.dumps([w['slug'] for w in works])
    (SCORES/'legacy-links.js').write_text('const scoreSlugs = '+sections+';\nconst oldSlug = location.hash.slice(1);\nif (scoreSlugs.includes(oldSlug)) location.replace("/scores/work/" + oldSlug + "/");\n')
    focus=[w for w in works if w['priority']<999]
    desc='高校民族乐团的简谱与总谱资源。查秦兵马俑、太阳颂、五声组曲等整曲合订本和固定调、首调独立分谱，查官方谱源及编制工具。'
    links='<div class="hero-actions">'+anchor('/scores/library/','查民乐简谱分谱','button primary')+anchor('/scores/sources/','找官方总谱','button')+'</div>'
    note=f'<aside class="hero-note"><h2>谱库收录</h2><p><strong>{len(works)} 个简谱版本</strong> · {sum(w["partCount"] for w in works):,} 份独立分谱</p><p>{len(opens)} 份开放谱本 · {len(sources)} 条原机构入口</p></aside>'
    search = '<form class="site-search" method="get" action="/scores/search/"><label for="home-q">搜索谱库</label><div><input id="home-q" name="q" type="search" maxlength="180" placeholder="曲名、作曲家、乐器或机构"><button class="button primary" type="submit">搜曲谱</button></div></form>'
    home=hero('高校民族乐团乐谱资源','找谱、看编制、准备排练','查找民族管弦乐简谱、民乐与中西混编曲目。按曲目核对谱种、声部、版次和原谱来源。',search+links,note)
    home+=block('大型作品与分乐章套谱',grid([work_card(w,False) for w in focus])+f'<p class="actions">{anchor("/scores/library/","查看全部已发布简谱","button")}</p>')
    home+=block('练团与制谱',grid([
        card('免费谱库','查看具体版次和许可，直接到原站获取公版及开放总谱。','/scores/open/'),
        card('按乐器找分谱','用乐器名找到曲目，再核对乐章、简谱版本和实际页数。','/scores/instruments/'),
        card('编制与自适应编曲','检查现有编制的声部覆盖，或导入 MusicXML 试配。','/scores/tools/'),
        card('排练与校谱','从选曲、发谱、翻页到修订交接，使用可打印验收清单。','/scores/guides/'),
        card('民乐与中西混编','查看《大东北我的家乡》的三个编制和《La La Land》案例。','/scores/arrangements/'),
        card('高校共建','准备试奏反馈、校谱记录或原创编配合作草稿。','/scores/tools/cooperation/'),
    ]))
    output('/scores/','高校民乐简谱与民族管弦乐总谱',desc,home,script='/scores/legacy-links.js',schema={'@context':'https://schema.org','@type':'WebSite','name':TITLE,'url':BASE+'/scores/'})
    work_pages(works,parts)
    instruments_page(works,roster_data['families'])
    open_pages(opens)
    source_page(sources)
    search_page(works,opens,sources)
    for key,title,copy,subset in [('/scores/library/','专业谱库','查找已发布简谱，按曲名、乐器、编制或谱面版本筛选。',works),
                                 ('/scores/arrangements/','民乐与中西混编案例','按同一作品的不同编制比较谱件数量和交付形式。', [w for w in works if w['kind']=='编配版本'])]:
        link=f'<div class="hero-actions">{anchor("/scores/instruments/","按乐器找分谱","button")}</div>' if key=='/scores/library/' else ''
        output(key,title,copy+' 包含固定调和首调分谱、合订本及实际登记的指挥简谱总谱。',hero('曲目与版本',title,copy,link)+score_community.access_notice()+
            filtered([work_card(w) for w in subset],[w['kind'] for w in subset],[w['ensemble'] for w in subset],extra_filters=[('format','谱面版本',[v for w in subset for v in w['variants']]+(['简谱指挥总谱'] if any(w['fullScores'] for w in subset) else []))]),script='/scores/filters.js')
    import orchestra_showcase
    orchestra_showcase.build_showcase(sys.modules[__name__])
    score_community.build_community(sys.modules[__name__])
    import score_experience
    score_experience.build_experience(sys.modules[__name__],works,opens,sources)
    write_sitemap()
    print(f'{len(works)} protected works, {len(opens)} open editions, {len(sources)} catalogue entries, {len(GENERATED_PAGES)} indexable pages')
if __name__=='__main__':
    main()
