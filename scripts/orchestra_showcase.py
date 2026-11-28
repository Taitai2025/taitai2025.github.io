"""Build the evidence-backed university orchestra showcase.

Integration: ``build_showcase(api)`` before the main generator writes its sitemap.
The shared ``api.output`` supplies navigation, styles and route registration; this
module owns only /scores/orchestras/ and never changes the shared shell.
"""

from html import escape
import json
from pathlib import Path
import re
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = '/scores/orchestras/'
DATA = ROOT / 'scores/orchestras/data.json'
STYLE = '/scores/orchestras/showcase.css'
SCRIPT = '/scores/orchestras/showcase.js'
CONTACT = '/scores/tools/cooperation/#cooperation'

INTAKE_TEMPLATE = '''高校乐团风采 · 收录资料草稿

此文件是资料准备模板；下载或填写不会自动提交。
请核对后，通过国乐谱汇“校谱反馈与共建”页面联系维护者。
https://taitai2025.github.io/scores/tools/cooperation/#cooperation

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

如果提供人数、届数等会变化的数据，请注明统计时点。
请使用机构公开联系方式，不必附个人 QQ、手机或其他私人名单。
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
    parsed = urlparse(value)
    require(parsed.scheme == 'https' and parsed.hostname in {'www.bilibili.com', 'space.bilibili.com', 'mp.weixin.qq.com'}, f'Unexpected source URL: {value}')
    require(not parsed.username and not parsed.password and not parsed.port, f'Unexpected URL authority: {value}')
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
        for field in ('name', 'shortName', 'englishName', 'university', 'country', 'countryCode', 'city', 'province', 'summary', 'foundedLabel'):
            require(isinstance(entry.get(field), str) and entry[field].strip(), f'{slug}: missing {field}')
        require(bool(re.fullmatch(r'\d{4}-(?:0[1-9]|1[0-2])', entry.get('founded', ''))), f'{slug}: invalid founding date')
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
                require(photo['sourceUrl'][2:] in home_ids, f'Missing photo source anchor: {photo["sourceUrl"]}')
        require(len({photo['src'] for photo in entry['gallery']}) == len(entry['gallery']), f'{slug}: duplicate gallery image')
        urls = set()
        for video in entry.get('videos', []):
            checked_url(video['url'])
            require(bool(re.fullmatch(r'https://www\.bilibili\.com/video/BV[0-9A-Za-z]{10}/', video['url'])), f'{slug}: invalid Bilibili video URL')
            require(video['url'] not in urls, f'{slug}: duplicate performance')
            urls.add(video['url'])
            require(isinstance(video['year'], int) and 2000 <= video['year'] <= 2100 and video['title'] and video['kind'], f'{slug}: incomplete performance')
        require(urls, f'{slug}: no documented performances')
        for key in ('article', 'officialBilibili', 'imageArchive'):
            checked_url(entry['sources'][key]['url'])
        require('publicationDate' in entry['sources']['article'], f'{slug}: source date must be explicit, including null when unknown')
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
    api.output(route, title, description, body, active=DIRECTORY, script=SCRIPT, schema=schema)
    path = api.REPO / route.strip('/') / 'index.html'
    head = f'<link rel="stylesheet" href="{STYLE}"><meta property="og:image" content="{e(api.BASE + photo["src"])}"><meta property="og:image:alt" content="{e(photo["alt"])}"><meta property="og:image:width" content="{photo["width"]}"><meta property="og:image:height" content="{photo["height"]}"><meta name="twitter:card" content="summary_large_image">'
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
    <div class="actions"><a class="button primary" href="{CONTACT}">准备乐团收录资料 <span aria-hidden="true">↗</span></a><a class="button" href="{DIRECTORY}intake-template.txt" download>下载资料模板</a></div>
    <p class="orchestra-fine">共建页面会生成可检查的本地草稿，由你确认后发送；点击或下载不会自动提交资料。</p></div></section>'''


def directory_body(entries):
    featured = entries[0]
    total = len(entries)
    countries = sorted({(item['countryCode'], item['country']) for item in entries})
    options = ''.join(f'<option value="{e(code)}">{e(name)}</option>' for code, name in countries)
    cards = []
    for n, item in enumerate(entries, 1):
        route = DIRECTORY + item['slug'] + '/'
        search = ' '.join([item['name'], item['englishName'], item['shortName'], item['nickname'], item['university'], item['country'], item['province'], item['city'], *item['aliases']])
        cards.append(f'''<article class="orchestra-directory-card" data-showcase-entry data-search="{e(search)}" data-country="{e(item['countryCode'])}">
        <a href="{route}" class="orchestra-card-image" aria-label="走进{e(item['name'])}">{photo_html(item['hero'])}<span class="orchestra-image-label">{e(item['shortName'])} <span aria-hidden="true">↗</span></span></a>
        <div class="orchestra-card-copy"><div class="orchestra-card-top"><span class="orchestra-number">{n:02d}</span><span>{e(item['country'])} · {e(item['city'])}</span></div><h3>{link(route, item['name'])}</h3><p class="orchestra-english" lang="en">{e(item['englishName'])}</p><p>{e(item['summary'])}</p><p class="orchestra-card-fact">始于 {e(item['foundedLabel'])} <span aria-hidden="true">·</span> 高校学生民族乐团</p><a href="{route}" class="orchestra-story-link">走进 {e(item['shortName'])}<span aria-hidden="true">→</span></a></div></article>''')
    return f'''<div class="orchestra-showcase">
    <section class="orchestra-directory-hero"><div class="shell orchestra-directory-intro"><div>
    {breadcrumbs([('高校乐团风采', '')])}<p class="eyebrow">UNIVERSITY CHINESE ORCHESTRAS</p><h1>高校乐团风采</h1><p class="orchestra-hero-line">在世界的校园里，<br>听见中国乐器。</p><p class="orchestra-lede">走进一支乐团，听它的舞台，也看它的日常。这里收集高校民族乐团的故事、实景照片与音乐会回看，让校园里的热爱彼此相见。</p>
    <div class="actions"><a href="#orchestra-list" class="button primary">探索已收录乐团 <span aria-hidden="true">↓</span></a><a href="#contribute" class="orchestra-inline-link">分享你们的乐团</a></div><p class="orchestra-collection-note">面向全球高校持续征集 · 当前收录 {total} 支乐团</p></div>
    <figure class="orchestra-directory-photo">{photo_html(featured['cover'], eager=True)}<figcaption><span>{e(featured['cover']['caption'])}</span><span>{e(featured['shortName'])} · {e(featured['city'])}</span></figcaption></figure></div></section>
    <section class="shell orchestra-section" id="orchestra-list" aria-labelledby="orchestra-list-title" data-showcase-filter data-query-key="q" data-facet-key="country" data-unit="支乐团">
    <div class="orchestra-section-heading"><div><p class="eyebrow">从真实的校园故事开始</p><h2 id="orchestra-list-title">遇见一支乐团</h2></div><p>每一份介绍都有可追溯的出处。<br>从中国科大 NMOU 开始，逐步走向更多校园。</p></div>
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
        <figcaption><div><span class="orchestra-photo-date">{e(photo['dateLabel'])}</span><h3>{e(photo['caption'])}</h3></div><a href="{e(photo['sourceUrl'])}" class="orchestra-photo-source">图像记录 <span aria-hidden="true">↗</span></a></figcaption></figure>''')
        dots.append(f'<button type="button" data-gallery-to="{index}" aria-controls="{track_id}" aria-label="转到第 {number} 张：{e(photo["caption"])}"><span>{number:02d}</span></button>')
    return f'''<section class="orchestra-gallery-section" id="photographs" aria-labelledby="photographs-title"><div class="shell">
    <div class="orchestra-section-heading"><div><p class="eyebrow">舞台 · 排练 · 校园</p><h2 id="photographs-title">让照片说说小乐的日常</h2></div><p>一场演出之前，是一次次练习与相聚。<br>横向滑动浏览，或点开照片查看原图。</p></div>
    <div class="orchestra-gallery" data-orchestra-gallery role="region" aria-roledescription="图片轮播" aria-label="{e(item['shortName'])} 影像记录">
    <p class="sr-only" id="{track_id}-help">图片列表获得焦点时，可使用左右方向键切换，Home 回到第一张，End 前往最后一张。图片不会自动播放。</p>
    <div class="orchestra-gallery-track" id="{track_id}" tabindex="0" aria-label="乐团照片列表" aria-describedby="{track_id}-help" data-gallery-track>{''.join(slides)}</div>
    <div class="orchestra-gallery-controls" hidden data-gallery-controls><div class="orchestra-gallery-arrows"><button type="button" data-gallery-prev aria-controls="{track_id}" aria-label="上一张照片"><span aria-hidden="true">←</span></button><button type="button" data-gallery-next aria-controls="{track_id}" aria-label="下一张照片"><span aria-hidden="true">→</span></button></div><div class="orchestra-gallery-dots" aria-label="选择照片">{''.join(dots)}</div><p class="orchestra-gallery-status" data-gallery-status role="status" aria-live="polite" aria-atomic="true">1 / {len(photos)}</p></div></div>
    <p class="orchestra-fine">图注与日期来自原有活动记录。照片未标日期时保留说明；点击“图像记录”可回到原出处。</p></div></section>'''


def videos_html(item):
    years = sorted({video['year'] for video in item['videos']}, reverse=True)
    options = ''.join(f'<option value="{year}">{year} 年</option>' for year in years)
    cards = []
    for video in item['videos']:
        search = ' '.join([str(video['year']), video['title'], video['kind'], item['shortName'], item['name']])
        cards.append(f'''<article class="orchestra-video" data-showcase-entry data-search="{e(search)}" data-year="{video['year']}"><div class="orchestra-video-top"><span class="orchestra-video-year">{video['year']}</span><span class="orchestra-video-kind">{e(video['kind'])}</span></div><h3><a href="{e(video['url'])}" target="_blank" rel="noopener noreferrer">{e(video['title'])}<span class="sr-only">，{video['year']} 年，在 B 站新窗口观看</span></a></h3><p><span class="orchestra-play" aria-hidden="true">▷</span> 在 B 站观看 <span aria-hidden="true">↗</span></p></article>''')
    return f'''<section class="shell orchestra-section" id="performances" aria-labelledby="performances-title" data-showcase-filter data-query-key="vq" data-facet-key="year" data-unit="场演出">
    <div class="orchestra-section-heading"><div><p class="eyebrow">从一场音乐会开始听</p><h2 id="performances-title">演出回看</h2></div><div><p>专场、独奏与主题音乐会，<br>按年份寻找一段想听的声音。</p>{external_button(item['sources']['officialBilibili']['url'], '前往 NMOU 官方 B 站')}</div></div>
    <form class="orchestra-filter" hidden data-showcase-form role="search" aria-label="筛选音乐会"><label class="orchestra-search">搜索音乐会<input type="search" name="vq" maxlength="180" data-showcase-search placeholder="如 青风抚乐、独奏、ACG"></label><label>演出年份<select name="year" data-showcase-select><option value="">全部年份</option>{options}</select></label><button type="reset" class="button">清除筛选</button></form>
    <p class="orchestra-filter-status" data-showcase-status role="status" aria-live="polite">已整理 {len(item['videos'])} 场演出链接</p><div class="orchestra-video-grid">{''.join(cards)}</div><div class="orchestra-empty" data-showcase-empty hidden><h3>还没有匹配的演出</h3><p>试试更短的音乐会名称，或切换为全部年份。</p><button type="button" class="button" data-showcase-reset>清除筛选</button></div>
    <p class="orchestra-fine">以上为已整理的公开演出入口，不代表乐团完整演出史。视频在 B 站新窗口打开；播放与可用性以原平台为准。</p></section>'''


def detail_body(item):
    source = item['sources']
    source_date = source['article']['publicationDate'] or '尚未确认'
    article_url = source['article']['url']
    display_name = e(item['name'])
    if item['name'].startswith(item['university']):
        display_name = e(item['university']) + '<br>' + e(item['name'][len(item['university']):])
    story = ''.join(f'<p>{e(paragraph)}</p>' for paragraph in item['intro'])
    timeline = []
    anniversary = next((video['url'] for video in item['videos'] if video['title'] == '岁影辰辉'), article_url)
    for record in item['timeline']:
        url = anniversary if record['source'] == 'anniversary' else article_url
        timeline.append(f'<li><span class="orchestra-timeline-date">{e(record["date"])}</span><h3>{e(record["title"])}</h3><p>{e(record["copy"])}</p>{link(url, "查看出处 ↗", "orchestra-source-link", external=True)}</li>')
    sections = ''.join(f'<li><strong>{e(section["name"])}</strong><span>{e(section["line"])}</span></li>' for section in item['sections'])
    life = ''.join(f'<article><span class="orchestra-life-number">0{index}</span><p class="eyebrow">{e(record["label"])}</p><h3>{e(record["title"])}</h3><p>{e(record["copy"])}</p></article>' for index, record in enumerate(item['life'], 1))
    return f'''<div class="orchestra-showcase">
    <section class="orchestra-detail-hero"><div class="shell">{breadcrumbs([('高校乐团风采', DIRECTORY), (item['shortName'], '')])}
    <div class="orchestra-detail-title"><div><p class="eyebrow">{e(item['country'])} · {e(item['province'])} · {e(item['city'])}</p><h1>{display_name}</h1><p class="orchestra-detail-english" lang="en">{e(item['englishName'])}</p></div><div class="orchestra-monogram" aria-label="简称 {e(item['shortName'])}"><span>{e(item['shortName'])}</span><p>我们的{e(item['nickname'])}</p></div></div>
    <p class="orchestra-detail-lede">从一次合奏，到一段共同的大学时光。</p><div class="actions"><a class="button orchestra-hero-button" href="#performances">听一场音乐会 <span aria-hidden="true">↓</span></a>{external_button(source['officialBilibili']['url'], '乐团官方 B 站')}</div>
    <figure class="orchestra-hero-photo">{photo_html(item['hero'], eager=True)}<figcaption><span>{e(item['hero']['caption'])}</span><span>{e(item['hero']['dateLabel'])}</span></figcaption></figure></div></section>
    <div class="orchestra-jump"><nav class="shell" aria-label="本页章节"><a href="#story">乐团故事</a><a href="#photographs">影像记录</a><a href="#performances">演出回看</a><a href="#sources">参与与来源</a></nav></div>
    <section class="shell orchestra-section" id="story" aria-labelledby="story-title"><div class="orchestra-story-grid"><article class="orchestra-story-copy"><p class="eyebrow">认识 {e(item['shortName'])}</p><h2 id="story-title">因为国乐，<br>我们在这里相遇。</h2>{story}<ul class="orchestra-voices" aria-label="乐团声部">{sections}</ul></article><aside class="orchestra-history" aria-labelledby="history-title"><p class="eyebrow">一些留下来的时刻</p><h2 id="history-title">从 {e(item['founded'][:4])} 年开始</h2><ol>{''.join(timeline)}</ol></aside></div>
    <div class="orchestra-life-grid">{life}</div></section>
    {gallery_html(item)}{videos_html(item)}
    <section class="orchestra-source-section" id="sources" aria-labelledby="sources-title"><div class="shell orchestra-source-grid"><div><p class="eyebrow">把热爱继续下去</p><h2 id="sources-title">传承经典，创新未来。</h2><p>{e(source['outlook'])}</p><div class="actions">{external_button(source['officialBilibili']['url'], '关注乐团动态', primary=True)}{external_button(article_url, '阅读乐团介绍原文')}</div></div><aside class="orchestra-source-note"><h3>关于这份乐团档案</h3><p>{e(source['note'])}</p><dl><dt>文字来源</dt><dd>{link(article_url, source['article']['label'], external=True)}</dd><dt>原稿编辑</dt><dd>{e(source['article']['editor'])}</dd><dt>原文发布日期</dt><dd>{e(source_date)}</dd><dt>图像记录</dt><dd>{link(source['imageArchive']['url'], source['imageArchive']['label'])}</dd></dl><p>发现内容或图注需要更新？{link(CONTACT, '准备更正资料', 'orchestra-inline-link')}。</p></aside></div></section>
    {contribution_panel(compact=True)}</div>'''


def build_showcase(api):
    entries = load_data()
    base = api.BASE
    directory_schema = {
        '@context': 'https://schema.org',
        '@graph': [
            {'@type': 'CollectionPage', '@id': base + DIRECTORY, 'url': base + DIRECTORY, 'name': '高校乐团风采｜国乐谱汇', 'description': '面向全球高校征集民族乐团故事、实景照片与音乐会回看，当前从中国科学技术大学 NMOU 开始收录。', 'inLanguage': 'zh-CN', 'mainEntity': {'@type': 'ItemList', 'numberOfItems': len(entries), 'itemListElement': [{'@type': 'ListItem', 'position': n, 'url': base + DIRECTORY + item['slug'] + '/', 'name': item['name']} for n, item in enumerate(entries, 1)]}},
            breadcrumb_schema(base, [('高校乐团风采', DIRECTORY)]),
        ],
    }
    emit(api, DIRECTORY, '高校乐团风采 · 校园里的中国声音', '走进高校民族乐团的舞台与日常，浏览真实活动照片、音乐会回看与资料出处。当前收录中国科学技术大学 NMOU，面向全球高校持续征集。', directory_body(entries), directory_schema, entries[0]['cover'])
    for item in entries:
        route = DIRECTORY + item['slug'] + '/'
        group_id = base + route + '#orchestra'
        schema = {
            '@context': 'https://schema.org',
            '@graph': [
                {'@type': 'WebPage', '@id': base + route, 'url': base + route, 'name': item['name'] + ' ' + item['shortName'] + '｜国乐谱汇', 'description': item['summary'], 'inLanguage': 'zh-CN', 'about': {'@id': group_id}, 'primaryImageOfPage': {'@type': 'ImageObject', 'contentUrl': base + item['hero']['src'], 'caption': item['hero']['caption']}, 'citation': [{'@type': 'CreativeWork', 'url': item['sources']['article']['url'], 'name': item['sources']['article']['label']}]},
                {'@type': 'MusicGroup', '@id': group_id, 'name': item['name'], 'alternateName': [item['englishName'], item['shortName'], item['nickname']], 'url': base + route, 'foundingDate': item['founded'], 'description': item['summary'], 'genre': '中国民族音乐', 'sameAs': [item['sources']['officialBilibili']['url']], 'memberOf': {'@type': 'CollegeOrUniversity', 'name': item['university']}, 'image': base + item['hero']['src']},
                breadcrumb_schema(base, [('高校乐团风采', DIRECTORY), (item['name'], route)]),
            ],
        }
        description = f'认识{item["name"]} {item["shortName"]}：{item["foundedLabel"]}成立，了解乐团故事与校园活动，浏览 {len(item["gallery"])} 张真实活动照片和 {len(item["videos"])} 场音乐会回看入口。'
        emit(api, route, item['name'] + ' ' + item['shortName'] + ' · 乐团故事与音乐会回看', description, detail_body(item), schema, item['hero'])
    target = api.REPO / 'scores/orchestras/intake-template.txt'
    target.write_text(INTAKE_TEMPLATE, encoding='utf-8')
    return [DIRECTORY, *(DIRECTORY + item['slug'] + '/' for item in entries)]
