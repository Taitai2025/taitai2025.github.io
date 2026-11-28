"""Build the evidence-backed university orchestra showcase.

Integration: ``build_showcase(api)`` before the main generator writes its sitemap.
The shared ``api.output`` supplies navigation, styles and route registration; this
module owns only /scores/orchestras/ and never changes the shared shell.
"""

from html import escape
from hashlib import sha256
import json
from pathlib import Path
import re
from urllib.parse import quote, urlparse

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = '/scores/orchestras/'
DATA = ROOT / 'scores/orchestras/data.json'
STYLE = '/scores/orchestras/showcase.css'
SCRIPT = '/scores/orchestras/showcase.js'
CONTACT = '/scores/orchestras/submit/'
CONTACT_DETAILS = json.loads((ROOT / 'scores/community/config.json').read_text(encoding='utf-8'))
INTAKE_EMAIL = CONTACT_DETAILS['email']
INTAKE_WECHAT = CONTACT_DETAILS['wechat']
INTAKE_QQ = CONTACT_DETAILS['qq']
INTAKE_MAILTO = 'mailto:' + INTAKE_EMAIL + '?subject=' + quote('【国乐谱汇·高校乐团投稿】学校与乐团名称')

INTAKE_TEMPLATE = f'''高校乐团风采 · 收录资料草稿

此文件是资料准备模板；下载或填写不会自动提交。
请核对后，将资料与照片作为附件发至 {INTAKE_EMAIL}。
邮件主题建议：【国乐谱汇·高校乐团投稿】学校与乐团名称
也可联系站点维护者：微信 {INTAKE_WECHAT} / QQ {INTAKE_QQ}。
专属收录页面：https://taitai2025.github.io{CONTACT}

乐团正式名称：
英文名称、简称或昵称（可选）：
所属高校：
国家或地区 / 城市：
成立年月及可核对的出处：
乐团简介与特点：
声部与主要活动：
官方主页或公开账号：
音乐会名称、年份及官方公开视频链接：
图片名称、实际内容、拍摄时间、摄影者（如已知）：
图片出处与展示授权范围：
介绍文字出处与授权范围：
资料核对日期：
需要更新或尚不能确认的部分：
投稿人的身份、与乐团的关系及回复联系方式（仅用于核对，不默认公开）：

如果提供人数、届数等会变化的数据，请注明统计时点。
乐团公开联系入口请使用机构账号，不必附团员私人 QQ、手机或内部名单。
请确认有权分享所提交的文字与照片，并说明允许本站公开展示的范围。
提交后由维护者人工核对；发送邮件不会自动发布网页。
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked_url(value, *, image=False):
    require(isinstance(value, str), 'URL must be text')
    if image:
        require(bool(re.fullmatch(r'/assets/images/music/[a-z0-9-]+\.webp', value)), f'Unexpected image path: {value}')
        return value
    if value.startswith('/#'):
        require(bool(re.fullmatch(r'/#[a-z0-9-]+', value)), f'Unexpected source anchor: {value}')
        return value
    if value == '#sources':
        return value
    parsed = urlparse(value)
    require(parsed.scheme == 'https' and parsed.hostname in {'www.bilibili.com', 'space.bilibili.com', 'mp.weixin.qq.com', 'taitai2025.github.io', 'www.nwpu.edu.cn', 'ysjyzx.nwpu.edu.cn'}, f'Unexpected source URL: {value}')
    require(not parsed.username and not parsed.password and not parsed.port, f'Unexpected URL authority: {value}')
    if parsed.hostname == 'taitai2025.github.io':
        require(bool(re.fullmatch(r'/assets/documents/(?:honors/)?[a-z0-9-]+\.pdf', parsed.path)), f'Unexpected public document: {value}')
        require(not parsed.query and (not parsed.fragment or bool(re.fullmatch(r'page=[1-9][0-9]*', parsed.fragment))), f'Unexpected document selector: {value}')
    return value


def load_data(path=DATA, *, check_assets=True):
    data = json.loads(Path(path).read_text(encoding='utf-8'))
    require(data.get('schemaVersion') == 1, 'Unsupported showcase schema')
    entries = data.get('orchestras')
    require(isinstance(entries, list) and entries, 'Showcase requires at least one real orchestra')
    slugs = set()
    home_ids = set(re.findall(r'\bid="([^"]+)"', (ROOT / 'index.html').read_text(encoding='utf-8'))) if check_assets else set()
    for entry in entries:
        slug = entry.get('slug', '')
        require(bool(re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', slug)) and slug not in slugs, 'Invalid or duplicate orchestra slug')
        slugs.add(slug)
        for field in ('name', 'shortName', 'university', 'country', 'countryCode', 'city', 'province', 'summary'):
            require(isinstance(entry.get(field), str) and entry[field].strip(), f'{slug}: missing {field}')
        if entry.get('founded'):
            require(bool(re.fullmatch(r'\d{4}(?:-(?:0[1-9]|1[0-2]))?', entry['founded'])), f'{slug}: invalid founding date')
            require(entry.get('foundedLabel'), f'{slug}: missing founding date label')
        for field in ('englishName', 'nickname'):
            require(entry.get(field) is None or isinstance(entry[field], str), f'{slug}: invalid optional {field}')
        require(entry.get('intro') and entry.get('sections') and entry.get('life') and entry.get('timeline'), f'{slug}: incomplete introduction')
        require(len(entry.get('gallery', [])) >= 2, f'{slug}: gallery needs at least two documented images')
        for photo in [entry['hero'], entry['cover'], *entry['gallery']]:
            checked_url(photo['src'], image=True)
            checked_url(photo['sourceUrl'])
            for key in ('alt', 'caption', 'dateLabel'):
                require(isinstance(photo.get(key), str) and photo[key].strip(), f'{slug}: photo missing {key}')
            require(all(isinstance(photo.get(key), int) and photo[key] > 0 for key in ('width', 'height')), f'{slug}: invalid image dimensions')
            if check_assets:
                require((ROOT / photo['src'].lstrip('/')).is_file(), f'Missing image: {photo["src"]}')
                if photo['sourceUrl'].startswith('/#'):
                    require(photo['sourceUrl'][2:] in home_ids, f'Missing photo source anchor: {photo["sourceUrl"]}')
            if photo['sourceUrl'] == '#sources':
                require(entry.get('sources', {}).get('submission'), f'{slug}: submitted image needs provenance')
        require(len({photo['src'] for photo in entry['gallery']}) == len(entry['gallery']), f'{slug}: duplicate gallery image')
        urls = set()
        for video in entry.get('videos', []):
            checked_url(video['url'])
            require(bool(re.fullmatch(r'https://www\.bilibili\.com/video/BV[0-9A-Za-z]{10}/', video['url'])), f'{slug}: invalid Bilibili video URL')
            require(video['url'] not in urls, f'{slug}: duplicate performance')
            urls.add(video['url'])
            require(isinstance(video['year'], int) and 2000 <= video['year'] <= 2100 and video['title'] and video['kind'], f'{slug}: incomplete performance')
        require(urls, f'{slug}: no documented performances')
        sources = entry.get('sources', {})
        require(sources.get('article') or sources.get('submission'), f'{slug}: missing primary introduction source')
        for key in ('article', 'officialBilibili', 'imageArchive', 'institution'):
            if sources.get(key):
                checked_url(sources[key]['url'])
                require(sources[key].get('label'), f'{slug}: missing {key} label')
        if sources.get('article'):
            require('publicationDate' in sources['article'], f'{slug}: source date must be explicit, including null when unknown')
        if sources.get('submission'):
            require(all(sources['submission'].get(key) for key in ('label', 'dateLabel', 'textCredit', 'imageCredit', 'displayNote')), f'{slug}: incomplete submission provenance')
        reference_ids = set()
        for reference in sources.get('references', []):
            require(reference.get('id') and reference['id'] not in reference_ids and reference.get('label'), f'{slug}: invalid source reference')
            reference_ids.add(reference['id'])
            checked_url(reference['url'])
            require('publicationDate' in reference, f'{slug}: missing reference date')
        for key, document in entry.get('documents', {}).items():
            checked_url(document['url'])
            require(document.get('title') and document.get('description'), f'{slug}: incomplete document {key}')
            require(isinstance(document.get('pages'), int) and document['pages'] > 0, f'{slug}: invalid document page count')
            require(bool(re.fullmatch(r'[a-f0-9]{64}', document.get('sha256', ''))), f'{slug}: missing document fingerprint')
        for record in entry.get('yearbook', []):
            require(all(record.get(key) for key in ('dateLabel', 'title', 'copy', 'document', 'sourceLabel')), f'{slug}: incomplete annual record')
            require(record['document'] in entry.get('documents', {}), f'{slug}: annual record missing evidence')
            require(isinstance(record.get('page'), int) and 1 <= record['page'] <= entry['documents'][record['document']]['pages'], f'{slug}: invalid evidence page')
        for record in entry.get('honors', []):
            require(record.get('title') and record.get('copy') and record.get('document') in entry.get('documents', {}), f'{slug}: incomplete honor evidence')
        for record in entry['timeline']:
            require(record.get('source') in {key for key in ('article', 'submission') if sources.get(key)} | {'anniversary', *entry.get('documents', {}), *reference_ids}, f'{slug}: unknown timeline source')
        require(sources.get('note') and sources.get('outlook'), f'{slug}: incomplete source notes')
        if 'updatedAt' in entry:
            require(bool(re.fullmatch(r'\d{4}-\d{2}-\d{2}', entry['updatedAt'])), f'{slug}: invalid update date')
    return entries


def e(value):
    return escape(str(value), quote=True)


def link(url, label, cls='', *, external=False):
    extra = ' target="_blank" rel="noopener noreferrer"' if external else ''
    class_attr = f' class="{e(cls)}"' if cls else ''
    return f'<a href="{e(url)}"{class_attr}{extra}>{e(label)}</a>'


def photo_html(photo, *, eager=False, extra_class=''):
    load = 'loading="eager" fetchpriority="high"' if eager else 'loading="lazy"'
    return f'<img class="{e(extra_class)}" src="{e(photo["src"])}" width="{photo["width"]}" height="{photo["height"]}" alt="{e(photo["alt"])}" {load} decoding="async">'


def external_button(url, text, *, primary=False):
    cls = 'button primary' if primary else 'button'
    return f'<a href="{e(url)}" class="{cls}" target="_blank" rel="noopener noreferrer">{e(text)} <span aria-hidden="true">↗</span><span class="sr-only">（在新窗口打开）</span></a>'


def breadcrumbs(items):
    links = '<li><a href="/scores/">国乐谱汇</a></li>'
    for label, url in items:
        links += '<li>' + (link(url, label) if url else f'<span aria-current="page">{e(label)}</span>') + '</li>'
    return f'<nav class="orchestra-breadcrumbs" aria-label="面包屑"><ol>{links}</ol></nav>'


def breadcrumb_schema(base, items):
    return {'@type': 'BreadcrumbList', 'itemListElement': [
        {'@type': 'ListItem', 'position': n, 'name': name, 'item': base + route}
        for n, (name, route) in enumerate([('国乐谱汇', '/scores/'), *items], 1)
    ]}


def emit(api, route, title, description, body, schema, photo):
    script_version = sha256((ROOT / SCRIPT.lstrip('/')).read_bytes()).hexdigest()[:12]
    style_version = sha256((ROOT / STYLE.lstrip('/')).read_bytes()).hexdigest()[:12]
    api.output(route, title, description, body, active=DIRECTORY, script=f'{SCRIPT}?v={script_version}', schema=schema)
    path = api.REPO / route.strip('/') / 'index.html'
    head = f'<link rel="stylesheet" href="{STYLE}?v={style_version}"><meta property="og:image" content="{e(api.BASE + photo["src"])}"><meta property="og:image:alt" content="{e(photo["alt"])}"><meta property="og:image:width" content="{photo["width"]}"><meta property="og:image:height" content="{photo["height"]}"><meta name="twitter:card" content="summary_large_image">'
    html = path.read_text(encoding='utf-8').replace('</head>', head + '</head>', 1)
    path.write_text(html, encoding='utf-8')


def contribution_panel(*, compact=False):
    intro = '欢迎世界各地的高校民族乐团分享自己的故事。资料经核对后逐步收录；本栏目收录不代表机构合作或推荐。'
    requirements = '' if compact else '''<ol class="orchestra-intake-list">
    <li><span>01</span><div><h3>一份有出处的介绍</h3><p>正式名称、所属高校、城市、成立时间与日常活动；易变化的数据请注明统计时点。</p></div></li>
    <li><span>02</span><div><h3>几张真实的乐团照片</h3><p>演出、排练或校园生活均可。说明图注、时间、出处及可公开展示的范围。</p></div></li>
    <li><span>03</span><div><h3>可以继续了解的入口</h3><p>乐团官方页面与音乐会视频，帮助读者找到后续活动与公开联系渠道。</p></div></li>
    </ol>'''
    return f'''<section class="orchestra-contribute" id="contribute" aria-labelledby="contribute-title"><div class="shell">
    <div class="orchestra-section-heading"><div><p class="eyebrow">一起留下校园里的中国声音</p><h2 id="contribute-title">下一站，是你的校园。</h2></div><p>{intro}</p></div>{requirements}
    <div class="actions"><a class="button primary" href="{CONTACT}">提交乐团资料</a><a class="button" href="{e(INTAKE_MAILTO)}">通过邮箱投稿</a><a class="button" href="{DIRECTORY}intake-template.txt" download>下载资料模板</a></div>
    <p class="orchestra-fine">专属收录页面提供资料清单、邮件草稿与微信 / QQ 联系方式。也可直接将介绍与照片发至 <a href="{e(INTAKE_MAILTO)}">{e(INTAKE_EMAIL)}</a>，由维护者核对后收录。点击或下载不会自动提交资料。</p></div></section>'''


def directory_body(entries):
    featured = entries[0]
    total = len(entries)
    countries = sorted({(item['countryCode'], item['country']) for item in entries})
    options = ''.join(f'<option value="{e(code)}">{e(name)}</option>' for code, name in countries)
    cards = []
    for n, item in enumerate(entries, 1):
        route = DIRECTORY + item['slug'] + '/'
        search = ' '.join([item['name'], item.get('englishName') or '', item['shortName'], item.get('nickname') or '', item['university'], item['country'], item['province'], item['city'], *item.get('aliases', [])])
        english = f'<p class="orchestra-english" lang="en">{e(item["englishName"])}</p>' if item.get('englishName') else ''
        founding = f'始于 {e(item["foundedLabel"])} <span aria-hidden="true">·</span> ' if item.get('founded') else ''
        group_type = e(item.get('groupType', '高校学生民族乐团'))
        cards.append(f'''<article class="orchestra-directory-card" data-showcase-entry data-search="{e(search)}" data-country="{e(item['countryCode'])}">
        <a href="{route}" class="orchestra-card-image" aria-label="走进{e(item['name'])}">{photo_html(item['hero'])}<span class="orchestra-image-label">{e(item['shortName'])} <span aria-hidden="true">↗</span></span></a>
        <div class="orchestra-card-copy"><div class="orchestra-card-top"><span class="orchestra-number">{n:02d}</span><span>{e(item['country'])} · {e(item['city'])}</span></div><h3>{link(route, item['name'])}</h3>{english}<p>{e(item['summary'])}</p><p class="orchestra-card-fact">{founding}{group_type}</p><a href="{route}" class="orchestra-story-link">走进 {e(item['shortName'])}<span aria-hidden="true">→</span></a></div></article>''')
    return f'''<div class="orchestra-showcase">
    <section class="orchestra-directory-hero"><div class="shell orchestra-directory-intro"><div>
    {breadcrumbs([('高校乐团风采', '')])}<p class="eyebrow">UNIVERSITY CHINESE ORCHESTRAS</p><h1>高校乐团风采</h1><p class="orchestra-hero-line">在世界的校园里，<br>听见中国乐器。</p><p class="orchestra-lede">走进一支乐团，听它的舞台，也看它的日常。这里收集高校民族乐团的故事、实景照片与音乐会回看，让校园里的热爱彼此相见。</p>
    <div class="actions"><a href="#orchestra-list" class="button primary">探索已收录乐团 <span aria-hidden="true">↓</span></a><a href="#contribute" class="orchestra-inline-link">分享你们的乐团</a></div><p class="orchestra-collection-note">面向全球高校持续征集 · 当前收录 {total} 支乐团</p></div>
    <figure class="orchestra-directory-photo">{photo_html(featured['cover'], eager=True)}<figcaption><span>{e(featured['cover']['caption'])}</span><span>{e(featured['shortName'])} · {e(featured['city'])}</span></figcaption></figure></div></section>
    <section class="shell orchestra-section" id="orchestra-list" aria-labelledby="orchestra-list-title" data-showcase-filter data-query-key="q" data-facet-key="country" data-unit="支乐团">
    <div class="orchestra-section-heading"><div><p class="eyebrow">从真实的校园故事开始</p><h2 id="orchestra-list-title">遇见一支乐团</h2></div><p>每一份介绍都有可追溯的出处。<br>从一座校园走向另一座校园，留下各自的声音。</p></div>
    <form class="orchestra-filter" hidden data-showcase-form role="search" aria-label="筛选高校乐团"><label class="orchestra-search">搜索乐团或学校<input type="search" maxlength="180" name="q" data-showcase-search placeholder="乐团、学校、简称或城市"></label><label>国家或地区<select name="country" data-showcase-select><option value="">全部已收录地区</option>{options}</select></label><button type="reset" class="button">清除筛选</button></form>
    <p class="orchestra-filter-status" role="status" aria-live="polite" data-showcase-status>当前收录 {total} 支乐团</p><div class="orchestra-directory-list">{''.join(cards)}</div>
    <div class="orchestra-empty" data-showcase-empty hidden><h3>还没有匹配的乐团</h3><p>试试学校简称、城市或英文缩写；也欢迎补充尚未收录的高校乐团。</p><div class="actions"><button type="button" class="button" data-showcase-reset>清除筛选</button><a href="#contribute" class="orchestra-inline-link">查看收录方式</a></div></div>
    <noscript><p class="orchestra-fine">全部已收录乐团已列在此页；启用 JavaScript 后可使用搜索筛选。</p></noscript></section>
    {contribution_panel()}</div>'''


def gallery_html(item):
    photos = item['gallery']
    slides = []
    dots = []
    track_id = item['slug'] + '-photos'
    for index, photo in enumerate(photos):
        number = index + 1
        slides.append(f'''<figure class="orchestra-gallery-slide" role="group" aria-roledescription="幻灯片" aria-label="第 {number} 张，共 {len(photos)} 张" data-gallery-slide>
        <a class="orchestra-gallery-image" href="{e(photo['src'])}" target="_blank" rel="noopener noreferrer" aria-label="查看原图：{e(photo['caption'])}（新窗口）">{photo_html(photo)}<span hidden class="orchestra-image-error" data-image-error>图片暂时无法加载，仍可阅读下方图注。</span><span class="orchestra-view-image" aria-hidden="true">查看原图 ↗</span></a>
        <figcaption><div><span class="orchestra-photo-date">{e(photo['dateLabel'])}</span><h3>{e(photo['caption'])}</h3></div><a href="{e(photo['sourceUrl'])}" class="orchestra-photo-source">{e(photo.get('sourceLabel', '图像记录'))} <span aria-hidden="true">↗</span></a></figcaption></figure>''')
        dots.append(f'<button type="button" data-gallery-to="{index}" aria-controls="{track_id}" aria-label="转到第 {number} 张：{e(photo["caption"])}"><span>{number:02d}</span></button>')
    return f'''<section class="orchestra-gallery-section" id="photographs" aria-labelledby="photographs-title"><div class="shell">
    <div class="orchestra-section-heading"><div><p class="eyebrow">舞台 · 排练 · 校园</p><h2 id="photographs-title">{e(item.get('galleryTitle', '舞台与校园的真实片段'))}</h2></div><p>一场演出之前，是一次次练习与相聚。<br>横向滑动浏览，或点开照片查看原图。</p></div>
    <div class="orchestra-gallery" data-orchestra-gallery role="region" aria-roledescription="图片轮播" aria-label="{e(item['shortName'])} 影像记录">
    <p class="sr-only" id="{track_id}-help">图片列表获得焦点时，可使用左右方向键切换，Home 回到第一张，End 前往最后一张。图片不会自动播放。</p>
    <div class="orchestra-gallery-track" id="{track_id}" tabindex="0" aria-label="乐团照片列表" aria-describedby="{track_id}-help" data-gallery-track>{''.join(slides)}</div>
    <div class="orchestra-gallery-controls" hidden data-gallery-controls><div class="orchestra-gallery-arrows"><button type="button" data-gallery-prev aria-controls="{track_id}" aria-label="上一张照片"><span aria-hidden="true">←</span></button><button type="button" data-gallery-next aria-controls="{track_id}" aria-label="下一张照片"><span aria-hidden="true">→</span></button></div><div class="orchestra-gallery-dots" aria-label="选择照片">{''.join(dots)}</div><p class="orchestra-gallery-status" data-gallery-status role="status" aria-live="polite" aria-atomic="true">1 / {len(photos)}</p></div></div>
    <p class="orchestra-fine">{e(item.get('galleryNote', '图注与日期来自原有活动记录。照片未标日期时保留说明；点击“图像记录”可回到原出处。'))}</p></div></section>'''


def videos_html(item):
    years = sorted({video['year'] for video in item['videos']}, reverse=True)
    options = ''.join(f'<option value="{year}">{year} 年</option>' for year in years)
    cards = []
    for video in item['videos']:
        search = ' '.join([str(video['year']), video['title'], video['kind'], item['shortName'], item['name']])
        note = f'<p class="orchestra-video-note">{e(video["note"])}</p>' if video.get('note') else ''
        cards.append(f'''<article class="orchestra-video" data-showcase-entry data-search="{e(search)}" data-year="{video['year']}"><div class="orchestra-video-top"><span class="orchestra-video-year">{video['year']}</span><span class="orchestra-video-kind">{e(video['kind'])}</span></div><h3><a href="{e(video['url'])}" target="_blank" rel="noopener noreferrer">{e(video['title'])}<span class="sr-only">，音乐会标示年份 {video['year']}，在 B 站新窗口观看</span></a></h3>{note}<p><span class="orchestra-play" aria-hidden="true">▷</span> 在 B 站观看 <span aria-hidden="true">↗</span></p></article>''')
    official = item['sources'].get('officialBilibili')
    official_button = external_button(official['url'], '前往 ' + official['label']) if official else ''
    return f'''<section class="shell orchestra-section" id="performances" aria-labelledby="performances-title" data-showcase-filter data-query-key="vq" data-facet-key="year" data-unit="场演出">
    <div class="orchestra-section-heading"><div><p class="eyebrow">从一场音乐会开始听</p><h2 id="performances-title">演出回看</h2></div><div><p>音乐会记录与精选演出片段，<br>按年份寻找一段想听的声音。</p>{official_button}</div></div>
    <form class="orchestra-filter" hidden data-showcase-form role="search" aria-label="筛选音乐会"><label class="orchestra-search">搜索音乐会<input type="search" name="vq" maxlength="180" data-showcase-search placeholder="音乐会名称、曲目或演出类型"></label><label>音乐会年份<select name="year" data-showcase-select><option value="">全部年份</option>{options}</select></label><button type="reset" class="button">清除筛选</button></form>
    <p class="orchestra-filter-status" data-showcase-status role="status" aria-live="polite">已整理 {len(item['videos'])} 场演出链接</p><div class="orchestra-video-grid">{''.join(cards)}</div><div class="orchestra-empty" data-showcase-empty hidden><h3>还没有匹配的演出</h3><p>试试更短的音乐会名称，或切换为全部年份。</p><button type="button" class="button" data-showcase-reset>清除筛选</button></div>
    <p class="orchestra-fine">{e(item.get('videoNote', '以上为已整理的公开演出入口，不代表乐团完整演出史。视频在 B 站新窗口打开；播放与可用性以原平台为准。'))}</p></section>'''


def yearbook_html(item):
    if not item.get('yearbook'):
        return ''
    documents = item['documents']
    records = []
    for record in item['yearbook']:
        url = documents[record['document']]['url'] + '#page=' + str(record['page'])
        records.append(f'''<article class="orchestra-yearbook-card"><p class="orchestra-record-date">{e(record['dateLabel'])}</p><h3>{e(record['title'])}</h3><p>{e(record['copy'])}</p>{link(url, record['sourceLabel'], 'orchestra-record-source', external=True)}</article>''')
    honors = ''.join(f'''<article class="orchestra-honor"><p class="eyebrow">团队荣誉</p><h3>{e(record['title'])}</h3><p>{e(record['copy'])}</p>{link(documents[record['document']]['url'], '查看获奖名单节选（PDF）', 'orchestra-record-source', external=True)}</article>''' for record in item.get('honors', []))
    readings = ''.join(f'''<li><a href="{e(doc['url'])}" target="_blank" rel="noopener noreferrer"><strong>{e(doc['title'])}</strong><span>{e(doc['description'])}</span><small>PDF · {doc['pages']} 页 · {e(doc['sizeLabel'])}</small></a></li>''' for doc in documents.values() if doc.get('reading'))
    return f'''<section class="shell orchestra-section orchestra-yearbook" id="yearbook" aria-labelledby="yearbook-title">
    <div class="orchestra-section-heading"><div><p class="eyebrow">2025—2026 学年 · 活动档案</p><h2 id="yearbook-title">舞台之外，国乐也在生长。</h2></div><p>从年度工作总结中选取已发生的活动，<br>让演出、教学与社区服务留下可以回看的记录。</p></div>
    <div class="orchestra-yearbook-grid">{''.join(records)}</div>
    <div class="orchestra-archive-grid"><div>{honors}</div><aside class="orchestra-reading" aria-labelledby="orchestra-reading-title"><h3 id="orchestra-reading-title">把经验留下来</h3><p>了解学生乐团怎样准备演出、开展教学与积累年度工作。</p><ul>{readings}</ul></aside></div>
    <p class="orchestra-fine">活动摘自 2026 年 5 月 8 日工作总结；教学资料为既有公开版本，包含相应学年的课程计划与实践记录。课程安排、负责人和招新信息请以乐团最新发布为准。</p></section>'''


def record_source(item, key):
    """Resolve a dated record to its public evidence or submission notes."""
    sources = item['sources']
    if key == 'submission':
        return '#sources', '投稿资料与日期说明'
    if key == 'article':
        return sources['article']['url'], '查看介绍原文 ↗'
    if key == 'anniversary':
        return next(video['url'] for video in item['videos'] if video['title'] == '岁影辰辉'), '查看纪念演出 ↗'
    if key in item.get('documents', {}):
        return item['documents'][key]['url'], '查看公开资料 ↗'
    reference = next(reference for reference in sources.get('references', []) if reference['id'] == key)
    return reference['url'], '查看学校报道 ↗'


def source_section_html(item):
    sources = item['sources']
    article = sources.get('article')
    submission = sources.get('submission')
    primary = sources.get('officialBilibili') or sources.get('institution')
    actions = external_button(primary['url'], primary['label'], primary=True) if primary else ''
    if article:
        actions += external_button(article['url'], '阅读乐团介绍原文')
    details = []
    if article:
        details.append(('文字来源', link(article['url'], article['label'], external=True)))
        if article.get('editor'):
            details.append(('原稿编辑', e(article['editor'])))
        details.append(('原文发布日期', e(article['publicationDate'] or '尚未确认')))
    if submission:
        details.extend([
            ('文字来源', e(submission['textCredit'])),
            ('影像来源', e(submission['imageCredit'])),
            ('资料时点', e(submission['dateLabel'])),
            ('展示说明', e(submission['displayNote'])),
        ])
    if sources.get('imageArchive'):
        archive = sources['imageArchive']
        details.append(('图像记录', link(archive['url'], archive['label'])))
    details.append(('档案整理日期', e(item.get('updatedAt', ''))))
    details_html = ''.join(f'<dt>{e(label)}</dt><dd>{value}</dd>' for label, value in details)
    references = ''.join(f'<li>{link(reference["url"], reference["label"], external=True)}<span>{e(reference.get("publicationDate") or "发布日期未确认")}</span></li>' for reference in sources.get('references', []))
    references_html = f'<div class="orchestra-public-sources"><h3>公开核对入口</h3><ul>{references}</ul></div>' if references else ''
    return f'''<section class="orchestra-source-section" id="sources" aria-labelledby="sources-title"><div class="shell orchestra-source-grid"><div><p class="eyebrow">把热爱继续下去</p><h2 id="sources-title">{e(sources.get('headline', '传承经典，创新未来。'))}</h2><p>{e(sources['outlook'])}</p><div class="actions">{actions}</div>{references_html}</div><aside class="orchestra-source-note"><h3>关于这份乐团档案</h3><p>{e(sources['note'])}</p><dl>{details_html}</dl><p>发现内容或图注需要更新？{link(CONTACT, '提交更正资料', 'orchestra-inline-link')}。</p></aside></div></section>'''


def detail_body(item):
    source = item['sources']
    display_name = e(item['name'])
    if item['name'].startswith(item['university']):
        display_name = e(item['university']) + '<br>' + e(item['name'][len(item['university']):])
    story = ''.join(f'<p>{e(paragraph)}</p>' for paragraph in item['intro'])
    timeline = []
    for record in item['timeline']:
        url, label = record_source(item, record['source'])
        timeline.append(f'<li><span class="orchestra-timeline-date">{e(record["date"])}</span><h3>{e(record["title"])}</h3><p>{e(record["copy"])}</p>{link(url, label, "orchestra-source-link", external=url.startswith("https://"))}</li>')
    sections = ''.join(f'<li><strong>{e(section["name"])}</strong><span>{e(section["line"])}</span></li>' for section in item['sections'])
    life = ''.join(f'<article><span class="orchestra-life-number">0{index}</span><p class="eyebrow">{e(record["label"])}</p><h3>{e(record["title"])}</h3><p>{e(record["copy"])}</p></article>' for index, record in enumerate(item['life'], 1))
    english = f'<p class="orchestra-detail-english" lang="en">{e(item["englishName"])}</p>' if item.get('englishName') else ''
    monogram_class = ' orchestra-monogram-long' if len(item['shortName']) > 4 else ''
    monogram_note = '我们的' + item['nickname'] if item.get('nickname') else item['university']
    history_title = item.get('historyTitle') or (f'从 {item["founded"][:4]} 年开始' if item.get('founded') else '一些留下来的时刻')
    official = source.get('officialBilibili')
    official_button = external_button(official['url'], official['label']) if official else '<a class="button" href="#sources">了解资料出处</a>'
    return f'''<div class="orchestra-showcase">
    <section class="orchestra-detail-hero"><div class="shell">{breadcrumbs([('高校乐团风采', DIRECTORY), (item['shortName'], '')])}
    <div class="orchestra-detail-title"><div><p class="eyebrow">{e(item['country'])} · {e(item['province'])} · {e(item['city'])}</p><h1>{display_name}</h1>{english}</div><div class="orchestra-monogram{monogram_class}" aria-label="简称 {e(item['shortName'])}"><span>{e(item['shortName'])}</span><p>{e(monogram_note)}</p></div></div>
    <p class="orchestra-detail-lede">{e(item.get('heroLine', '从一次合奏，到一段共同的大学时光。'))}</p><div class="actions"><a class="button orchestra-hero-button" href="#performances">听一场音乐会 <span aria-hidden="true">↓</span></a>{official_button}</div>
    <figure class="orchestra-hero-photo">{photo_html(item['hero'], eager=True)}<figcaption><span>{e(item['hero']['caption'])}</span><span>{e(item['hero']['dateLabel'])}</span></figcaption></figure></div></section>
    <div class="orchestra-jump"><nav class="shell" aria-label="本页章节"><a href="#story">乐团故事</a>{'<a href="#yearbook">年度记录</a>' if item.get('yearbook') else ''}<a href="#photographs">影像记录</a><a href="#performances">演出回看</a><a href="#sources">参与与来源</a></nav></div>
    <section class="shell orchestra-section" id="story" aria-labelledby="story-title"><div class="orchestra-story-grid"><article class="orchestra-story-copy"><p class="eyebrow">认识 {e(item['shortName'])}</p><h2 id="story-title">因为国乐，<br>我们在这里相遇。</h2>{story}<p class="orchestra-story-source">{link('#sources', '查看介绍与照片的资料出处', 'orchestra-inline-link')}</p><ul class="orchestra-voices" style="--voice-count:{len(item['sections'])}" aria-label="乐团声部">{sections}</ul></article><aside class="orchestra-history" aria-labelledby="history-title"><p class="eyebrow">一些留下来的时刻</p><h2 id="history-title">{e(history_title)}</h2><ol>{''.join(timeline)}</ol></aside></div>
    <div class="orchestra-life-grid">{life}</div></section>
    {yearbook_html(item)}{gallery_html(item)}{videos_html(item)}
    {source_section_html(item)}
    {contribution_panel(compact=True)}</div>'''


def build_showcase(api):
    entries = load_data()
    base = api.BASE
    directory_description = f'走进高校民族乐团的舞台与日常，浏览真实活动照片、音乐会回看与资料出处。当前收录 {len(entries)} 支乐团，面向全球高校持续征集。'
    directory_schema = {
        '@context': 'https://schema.org',
        '@graph': [
            {'@type': 'CollectionPage', '@id': base + DIRECTORY, 'url': base + DIRECTORY, 'name': '高校乐团风采｜国乐谱汇', 'description': directory_description, 'inLanguage': 'zh-CN', 'mainEntity': {'@type': 'ItemList', 'numberOfItems': len(entries), 'itemListElement': [{'@type': 'ListItem', 'position': n, 'url': base + DIRECTORY + item['slug'] + '/', 'name': item['name']} for n, item in enumerate(entries, 1)]}},
            breadcrumb_schema(base, [('高校乐团风采', DIRECTORY)]),
        ],
    }
    emit(api, DIRECTORY, '高校乐团风采 · 校园里的中国声音', directory_description, directory_body(entries), directory_schema, entries[0]['cover'])
    for item in entries:
        route = DIRECTORY + item['slug'] + '/'
        group_id = base + route + '#orchestra'
        sources = item['sources']
        references = ([sources['article']] if sources.get('article') else []) + sources.get('references', [])
        citations = [{'@type': 'CreativeWork', 'url': reference['url'], 'name': reference['label']} for reference in references]
        citations += [{'@type': 'CreativeWork', 'url': doc['url'], 'name': doc['title']} for doc in item.get('documents', {}).values()]
        if sources.get('submission'):
            citations.append({'@type': 'CreativeWork', 'name': sources['submission']['label']})
        group = {'@type': 'MusicGroup', '@id': group_id, 'name': item['name'], 'alternateName': list(dict.fromkeys(name for name in [item.get('englishName'), item['shortName'], item.get('nickname')] if name)), 'url': base + route, 'description': item['summary'], 'genre': '中国民族音乐', 'memberOf': {'@type': 'CollegeOrUniversity', 'name': item['university']}, 'image': base + item['hero']['src']}
        if item.get('founded'):
            group['foundingDate'] = item['founded']
        if sources.get('officialBilibili'):
            group['sameAs'] = [sources['officialBilibili']['url']]
        schema = {
            '@context': 'https://schema.org',
            '@graph': [
                {'@type': 'WebPage', '@id': base + route, 'url': base + route, 'name': item['name'] + ' ' + item['shortName'] + '｜国乐谱汇', 'description': item['summary'], 'inLanguage': 'zh-CN', 'about': {'@id': group_id}, 'primaryImageOfPage': {'@type': 'ImageObject', 'contentUrl': base + item['hero']['src'], 'caption': item['hero']['caption']}, 'citation': citations},
                group,
                breadcrumb_schema(base, [('高校乐团风采', DIRECTORY), (item['name'], route)]),
            ],
        }
        founding = f'{item["foundedLabel"]}成立，' if item.get('founded') else ''
        description = f'认识{item["name"]}：{founding}了解乐团故事与校园活动，浏览 {len(item["gallery"])} 张真实活动照片和 {len(item["videos"])} 个演出回看入口。'
        emit(api, route, item['name'] + ' ' + item['shortName'] + ' · 乐团故事与音乐会回看', description, detail_body(item), schema, item['hero'])
    target = api.REPO / 'scores/orchestras/intake-template.txt'
    target.write_text(INTAKE_TEMPLATE, encoding='utf-8')
    return [DIRECTORY, *(DIRECTORY + item['slug'] + '/' for item in entries)]
