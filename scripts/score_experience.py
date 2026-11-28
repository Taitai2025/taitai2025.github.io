"""Public-facing catalogue experience. All data passed here is already public."""
from html import escape
import json
import re
from urllib.parse import urlencode


def build_experience(api, works, opens, sources):
    records = []
    for work in works:
        records.append({
            'id': 'work:' + work['slug'], 'slug': work['slug'], 'kind': '已发布简谱',
            'title': work['title'], 'url': api.get_details(work), 'composer': work['composer'] or '署名待补录',
            'ensemble': work['ensemble'], 'format': '简谱分谱' + ('、独立简谱总谱' if work['fullScores'] else ''),
            'version': work['version'], 'partCount': work['partCount'],
            'instruments': list(dict.fromkeys(n for line in work['roster'] for n in line['instruments'])),
            'movements': work.get('movements', []), 'summary': work['summary'],
            'access': '已有口令下载', 'quality': work['quality'],
            'rehearsal': '尚未登记实际试奏', 'variants': work['variants'],
        })
    for work in opens:
        records.append({
            'id': 'open:' + work['slug'], 'slug': work['slug'], 'kind': '原站开放谱本',
            'title': work['title'], 'url': api.get_open(work), 'composer': work['composer'],
            'ensemble': work.get('format', '按原谱核对'), 'format': work.get('format', '按原谱核对'),
            'version': work['edition'], 'partCount': None, 'instruments': work.get('instruments', []), 'movements': [],
            'summary': work.get('details', ''), 'access': '到原站获取',
            'quality': '来源及谱种已登记', 'rehearsal': '移植或改编需另行准备', 'variants': [],
        })
    (api.SCORES / 'collection-index.json').write_text(json.dumps({'schemaVersion': 1, 'records': records}, ensure_ascii=False, indent=2) + '\n')

    def link(url, text, cls=''):
        return api.anchor(url, text, cls)

    def quick(query):
        return link('/scores/search/?' + urlencode({'q': query}), query, 'quick-link')

    featured = [w for w in works if w['priority'] < 999][:6]
    tiles = []
    for i, w in enumerate(featured):
        label = '分乐章套谱' if w.get('movements') else '整曲与独立分谱'
        tiles.append(f'''<article class="edition-card tone-{i % 3}" data-collection-card>
          <div class="edition-art" aria-hidden="true"><span>{escape(w['title'][:4])}</span><i></i><i></i><i></i><i></i></div>
          <div class="edition-content"><p class="eyebrow">{escape(w['ensemble'])}</p>
            <h3>{link(api.get_details(w), w['title'])}</h3><p>{escape(w['summary'])}</p>
            <div class="edition-meta"><span>{w['partCount']:,} 份分谱</span><span>{label}</span></div>
            <div class="edition-actions">{link(api.get_details(w), '查看版本与声部', 'text-link')}</div>
          </div></article>''')
    spotlight = works[0]
    if featured:
        spotlight = featured[0]
    home = f'''<section class="home-hero"><div class="frame home-grid">
      <div class="home-intro"><p class="eyebrow"><span class="small-rule"></span>为高校民族乐团而建</p>
        <h1>好作品，<br>从一份好谱开始。</h1>
        <p class="home-lede">查找民乐简谱、民族管弦乐总谱与中西混编作品。<br class="desktop-break">选对版本，核对编制，把时间留给音乐。</p>
        <form class="home-search" method="get" action="/scores/search/">
          <label class="sr-only" for="home-q">搜索曲名、乐器、谱式或机构</label>
          <svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="10.5" cy="10.5" r="6.5"/><path d="m15.5 15.5 5 5"/></svg>
          <input id="home-q" name="q" type="search" maxlength="180" placeholder="曲名、乐器、谱式或机构" autocomplete="off">
          <button class="button primary" type="submit">找谱</button>
        </form>
        <div class="quick-search"><span>试试</span>{quick('秦兵马俑')}{quick('高音笙 首调')}{quick('拉德茨基')}</div>
        <div class="home-directions">{link('/scores/library/', '浏览已发布简谱', 'text-link')}{link('/scores/sources/', '查找官方总谱来源', 'text-link')}</div>
      </div>
      <aside class="hero-feature"><div class="feature-top"><span>曲目精选</span><span>民族管弦乐</span></div>
        <div class="feature-art" aria-hidden="true"><div class="string-lines"><i></i><i></i><i></i><i></i><i></i><i></i></div><span class="feature-character">乐</span><span class="feature-seal">合奏</span></div>
        <div class="feature-bottom"><p>从声部到整曲，统一管理用谱</p><h2>{link(api.get_details(spotlight), spotlight['title'])}</h2><span>{spotlight['partCount']:,} 份独立分谱 · 固定调 / 首调</span></div>
      </aside>
    </div></section>
    <section class="stat-band" aria-label="谱库实际收录"><div class="frame stat-grid">
      <div><strong>{len(works)}</strong><span>已发布简谱版本</span></div><div><strong>{sum(w['partCount'] for w in works):,}</strong><span>独立分谱文件</span></div>
      <div><strong>{len(opens)}</strong><span>原站开放谱本</span></div><div><strong>{len(sources)}</strong><span>官方与馆藏入口</span></div>
    </div></section>
    <section class="shell home-section"><div class="section-heading"><div><p class="eyebrow">从熟悉的作品开始</p><h2>大型作品与分乐章套谱</h2></div>{link('/scores/library/', '查看全部简谱', 'text-link')}</div>
      <div class="edition-grid">{''.join(tiles)}</div><p class="section-caption">优先展示已有完整文件目录的大型作品。版本名称、文件核验与实际试奏记录分别列示。</p>
    </section>
    <section class="path-section"><div class="frame"><div class="section-heading"><div><p class="eyebrow">按这次排练的需要</p><h2>从这里，找到合适的谱</h2></div></div>
      <div class="path-grid">
        <a class="path-card" href="/scores/instruments/"><span class="path-symbol" aria-hidden="true">笙</span><h3>我想找某个声部</h3><p>按乐器进入曲目，核对首调、固定调和主旋律提示。</p><span class="text-link">按乐器找分谱</span></a>
        <a class="path-card" href="/scores/open/"><span class="path-symbol" aria-hidden="true">谱</span><h3>我想找免费原谱</h3><p>区分总谱、独奏谱和历史谱本，查看具体版本与取用方式。</p><span class="text-link">浏览开放谱本</span></a>
        <a class="path-card" href="/scores/tools/arrange/sections/"><span class="path-symbol" aria-hidden="true">合</span><h3>这次乐团人不齐</h3><p>导入 MusicXML / MXL，按实际席位试配，检查兼奏和翻页。</p><span class="text-link">打开分段试配</span></a>
        <a class="path-card" href="/scores/planner/"><span class="path-symbol" aria-hidden="true">选</span><h3>我在准备音乐会</h3><p>保存候选曲目、并排比较版本，整理曲序和排练备注。</p><span class="text-link">打开我的选曲单</span></a>
      </div></div></section>
    <section class="shell home-section"><div class="section-heading"><div><p class="eyebrow">原谱与改编，各有来处</p><h2>让找谱的路短一点</h2></div>{link('/scores/sources/', '全部总谱来源', 'text-link')}</div>
      <div class="resource-strip">
        <a href="/scores/sources/?q=香港中乐团"><span class="resource-monogram">港</span><div><h3>香港中乐团</h3><p>教育谱、经典作品与青年版本</p></div></a>
        <a href="/scores/sources/?q=新加坡"><span class="resource-monogram">新</span><div><h3>新加坡华乐团</h3><p>学校用谱与作品租借入口</p></div></a>
        <a href="/scores/open/"><span class="resource-monogram">典</span><div><h3>开放与历史谱本</h3><p>按原站许可和具体谱种取用</p></div></a>
      </div>
    </section>
    <section class="shell home-section"><div class="section-heading"><div><p class="eyebrow">认识演奏这些作品的人</p><h2>校园里，民乐正在发生</h2></div>{link('/scores/orchestras/', '高校乐团风采', 'text-link')}</div>
      <article class="orchestra-home-feature"><a class="orchestra-home-image" href="/scores/orchestras/ustc-nmou/"><img src="/assets/images/music/qingfeng-2025-curtain-call.webp" width="1600" height="1067" loading="lazy" decoding="async" alt="中国科大学生民族乐团在2025年青风抚乐专场音乐会谢幕合影"></a><div><p class="eyebrow">中国 · 合肥 · USTC</p><h3>中国科大学生民族乐团</h3><p class="orchestra-home-name">NMOU · 小乐</p><p>从每周的排练，到走上专场音乐会的舞台。认识这支创立于 2002 年的学生民族乐团，看看属于他们的音乐与青春。</p><div class="actions">{link('/scores/orchestras/ustc-nmou/', '走进 NMOU', 'button primary')}{link('/scores/orchestras/', '浏览乐团风采', 'text-link')}</div></div></article>
    </section>
    <section class="shell"><div class="cooperation-panel"><div><p class="eyebrow">把一次排练，变成下一版的进步</p><h2>一起把谱库做得更好</h2><p>记录小节、声部与版本，分享可复现的校谱问题；也欢迎原创编配与高校试用合作。</p></div><div class="actions">{link('/scores/tools/cooperation/', '准备反馈与合作资料', 'button primary')}{link('/scores/guides/rehearsal/', '查看排练指南', 'button')}</div></div></section>'''
    api.output('/scores/', '高校民乐简谱与民族管弦乐总谱', '国乐谱汇：高校民族乐团简谱、总谱与分谱资源。按曲名、乐器和编制查找固定调与首调版本，比较选曲，使用 MusicXML 编配和排练工具。', home,
               script='/scores/legacy-links.js', schema={'@context':'https://schema.org','@type':'WebSite','name':'国乐谱汇','url':api.BASE+'/scores/'})

    planner = api.hero('选曲与排练', '我的选曲单', '把候选曲目放在一起，比较谱式与编制，再整理曲序和排练备注。')
    planner += '''<section class="shell planner-shell" id="programme-app"><noscript><p class="callout">选曲单使用浏览器本地保存，需要启用 JavaScript。曲目详情和下载入口仍可直接访问。</p></noscript>
      <div class="planner-toolbar"><div><h2>这一场，想演什么？</h2><p class="muted">清单只保存在当前浏览器。下载 JSON 可备份或带到另一台设备。</p></div><div class="actions"><a class="button primary" href="/scores/library/">继续选曲</a><button type="button" class="button" id="import-plan">导入清单</button><input id="plan-file" type="file" accept=".json,application/json" hidden></div></div>
      <div class="plan-fields"><label>清单名称<input id="plan-title" maxlength="80" placeholder="例如：春季专场候选曲目"></label><label>计划日期<input type="date" id="plan-date"></label><label class="plan-notes">整体备注<textarea id="plan-notes" rows="2" maxlength="2000" placeholder="演出主题、到场编制或排练安排"></textarea></label></div>
      <div class="planner-summary" id="plan-summary" role="status"></div><div id="plan-list"></div>
      <div class="plan-bottom actions"><button type="button" class="button primary" id="compare-plan">比较所选版本</button><button type="button" class="button" id="export-plan">备份清单 JSON</button><button type="button" class="button" id="export-plan-csv">导出曲目表 CSV</button><button type="button" class="button" id="print-plan">打印选曲单</button></div>
      <p class="meta">时长由你填写，网站不推测曲目时长。此清单不包含乐谱文件，也不改变任何曲目的使用许可。</p>
    </section><dialog class="comparison-dialog" id="compare-dialog" aria-labelledby="compare-heading"><div class="dialog-heading"><h2 id="compare-heading">曲目与版本对照</h2><button type="button" class="button" id="close-comparison">关闭</button></div><div id="comparison-content" class="table-wrap"></div><p class="meta">编制名称相同不代表可以共用声部。最终以各版本的文件目录和原谱为准。</p></dialog>'''
    api.output('/scores/planner/', '我的选曲单与版本比较', '保存候选曲目，比较民族管弦乐与民乐混编版本，填写曲序、时长和排练备注，导出备份与可打印选曲单。', planner, index=True)

    about = api.hero('使用说明', '从找谱，到发谱', '给乐团谱务、指挥和演奏员的一份简明使用指南。')
    about += '''<section class="shell"><div class="cards two">
      <article class="card"><h2>已发布简谱</h2><p>进入曲目详情，先确认作品、编制和版本，再选合订本、独立分谱包或单列指挥总谱。合订本是各声部分谱的汇编，不等于指挥总谱。</p><p>分谱索引可查固定调、首调、带或不带主旋律提示，以及乐章和实际页数。已有口令资料沿用原领取方式。</p><a href="/scores/library/">浏览专业谱库</a></article>
      <article class="card"><h2>开放谱本与总谱导航</h2><p>开放谱库标注具体谱本、谱种与来源。历史工尺谱、古琴减字谱、西洋管弦乐总谱分别列示，不自动等同于现代民乐套谱。</p><p>原站免费提供下载，不自动授予商业改编或再分发权限。查看每条资源的许可与取用说明。</p><a href="/scores/sources/">查看原机构入口</a></article>
      <article class="card"><h2>选曲单与版本比较</h2><p>在曲目卡片或详情页点击“加入选曲单”。选曲单可调整曲序、记录时长和备注、比较最多四个版本，并导出 JSON、CSV 或打印。</p><p>清单保存在本浏览器，不会自动同步给其他团员。换设备或清除浏览器数据前，请先下载 JSON 备份。</p><a href="/scores/planner/">打开我的选曲单</a></article>
      <article class="card"><h2>编配工具的三个入口</h2><p>编制检查用于查看已有声部覆盖；整曲试配用于 MusicXML 声部与目标乐器的分配；分段试配进一步处理席位、缺席、兼奏与翻页。</p><p>结果用于编配与排练前的核对。可奏音域、原谱语义、实际乐器与音乐层次仍需确认，算法结果不会自动成为演出验收通过的成品。</p><a href="/scores/tools/">打开编制工具</a></article>
    </div></section>
    <section class="shell"><div class="section-head"><h2>怎样读懂版本与质量信息</h2></div><div class="table-wrap"><table><thead><tr><th>页面信息</th><th>表示什么</th><th>还应检查什么</th></tr></thead><tbody>
      <tr><th>版本名称</th><td>原交付件使用的版号与名称。</td><td>不要仅凭“终版”或“终审”推断实际试奏已经完成。</td></tr>
      <tr><th>文件核验</th><td>文件身份、数量、格式或相应清单的核对记录。</td><td>逐音内容校勘和现场排练分别记录。</td></tr>
      <tr><th>已知问题</th><td>来源记号、声部、分页或其他仍需确认的事项。</td><td>发谱前核对这些位置是否影响本团排练。</td></tr>
      <tr><th>实际排练</th><td>只记录已有依据的试奏情况。</td><td>未登记不等于没有任何人演过，也不等于已经通过验收。</td></tr>
    </tbody></table></div></section>
    <section class="shell"><div class="cards two"><article class="card"><h2>发现错音或下载问题</h2><p>记录曲名、版本、乐章、小节、声部和问题描述。下载异常请保留文件名与错误提示。反馈工具会生成可检查的草稿，使用者发送后才算提交。</p><div class="actions"><a class="button" href="/scores/tools/cooperation/">准备反馈草稿</a><a class="button" href="/scores/tools/rehearsal/">排练验收清单</a></div></article>
      <article class="card"><h2>数据与隐私</h2><p>本站的选曲、排练清单和本地编配设置在浏览器内保存；MusicXML/MXL 编配在本机处理。公开站没有收款表单，也不要求填写团员个人资料。</p><p>原机构链接会打开相应网站，按其说明使用。公开目录、私有谱务记录和真实交易授权分别维护。</p></article></div></section>
    <section class="shell"><div class="callout"><h2>本轮更新 · 2026 年 11 月 28 日</h2><p>重整首页与资源导航，补齐目录筛选和分谱搜索，增加选曲单及版本比较，接续 MusicXML/MXL 编配工具与维护校验。新的功能以实际可操作入口为准。</p><p><a href="/scores/guides/">继续阅读选曲、排练与许可指南</a></p></div></section>'''
    api.output('/scores/about/', '使用说明、版本与质量信息', '国乐谱汇使用说明：怎样找总谱与简谱、筛选声部、比较版本、备份选曲单、使用编配工具与反馈校谱问题。', about)

    # Hand-authored tool/guide pages use the same navigation and local planner.
    # Only replace the shell: each page keeps its own content and behaviour.
    for path in sorted(api.SCORES.rglob('index.html')):
        if '/archive/' in path.as_posix():
            continue
        text = path.read_text(encoding='utf-8')
        route = '/' + str(path.parent.relative_to(api.REPO)).replace('\\', '/') + '/'
        additions = []
        if '/scores/experience.css' not in text:
            additions.append('<link rel="stylesheet" href="/scores/experience.css">')
        if '/scores/experience.js' not in text:
            additions.append('<script src="/scores/experience.js" defer></script>')
        if '/scores/mark.svg' not in text:
            additions.append('<link rel="icon" type="image/svg+xml" href="/scores/mark.svg">')
        if additions:
            text = text.replace('</head>', '\n'.join(additions) + '\n</head>')
        text = re.sub(r'<header\b[^>]*class="site-header"[^>]*>.*?</header>', lambda m: api.head_links(route), text, count=1, flags=re.S)
        path.write_text(text, encoding='utf-8')
