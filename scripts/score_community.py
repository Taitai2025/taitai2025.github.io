"""Public contact, orchestra intake and voluntary support for the static site.

Forms prepare local drafts only. No submission endpoint, payment verification,
password storage or visitor-data persistence is implemented or implied here.
"""
from hashlib import sha256
from html import escape
import json
from pathlib import Path
from urllib.parse import urlencode, quote

ROOT = Path(__file__).resolve().parent.parent
CONFIG_PATH = ROOT / 'scores/community/config.json'


def config():
    return json.loads(CONFIG_PATH.read_text(encoding='utf-8'))


def e(value):
    return escape(str(value), quote=True)


def mailto(subject, body=''):
    return 'mailto:' + config()['email'] + '?' + urlencode({'subject': subject, 'body': body}, quote_via=quote)


def asset_url(name):
    path = ROOT / 'scores/community' / name
    return '/scores/community/' + name + '?v=' + sha256(path.read_bytes()).hexdigest()[:12]


def qr_image(key, alt):
    item = config()['assets'][key]
    return f'<img src="{item["src"]}" width="{item["width"]}" height="{item["height"]}" alt="{e(alt)}" loading="lazy" decoding="async">'


def contact_cards():
    c = config()
    return f'''<div class="community-contact-grid" id="channels">
      <article class="community-card"><p class="eyebrow">发送资料与附件</p><h2>邮箱</h2><a class="community-address" href="mailto:{e(c['email'])}">{e(c['email'])}</a><p>适合乐团介绍、照片原图与版本问题。主题里写上乐团或曲名，便于后续核对。</p><div class="actions"><a class="button primary" href="{e(mailto('国乐谱汇 · 资料与交流'))}">打开邮件应用</a><button hidden type="button" class="button" data-copy="{e(c['email'])}" data-copy-label="邮箱">复制邮箱</button></div><p class="community-small">备用邮箱：<a href="mailto:{e(c['backupEmail'])}">{e(c['backupEmail'])}</a></p></article>
      <article class="community-card" id="wechat"><p class="eyebrow">日常交流</p><h2>微信</h2><p class="community-address">{e(c['wechat'])}</p><p>添加时请备注“国乐谱汇＋乐团名 / 曲名”。可先说明需求，再发送相关资料。</p><div class="actions"><button hidden type="button" class="button" data-copy="{e(c['wechat'])}" data-copy-label="微信号">复制微信号</button></div><details class="community-qr"><summary>展开微信好友二维码</summary><figure>{qr_image('wechat-friend.jpg', '杨书泰的微信好友二维码，昵称泰泰，用于添加好友')}<figcaption>这是添加好友的二维码。</figcaption></figure><a href="/scores/community/wechat-friend.jpg" target="_blank" rel="noopener noreferrer">打开好友码原图</a></details></article>
      <article class="community-card" id="qq"><p class="eyebrow">日常交流</p><h2>QQ</h2><p class="community-address">{e(c['qq'])}</p><p>在 QQ 中搜索号码添加好友，备注学校、乐团与来意。谱子问题请附曲名、版本及声部。</p><button hidden type="button" class="button" data-copy="{e(c['qq'])}" data-copy-label="QQ 号">复制 QQ 号</button><p class="community-small">站点维护：{e(c['name'])}<br>联系方式与<a href="/#resume">个人主页</a>保持一致。</p></article>
    </div><p class="community-status" data-community-status role="status" aria-live="polite"></p>'''


def cooperation_contacts():
    c = config()
    return f'''<section class="tool-panel" aria-labelledby="direct-contact-title"><h2 id="direct-contact-title">资料可以直接发给我</h2><p>邮箱：<a href="mailto:{e(c['email'])}">{e(c['email'])}</a>；微信：{e(c['wechat'])}；QQ：{e(c['qq'])}。</p><div class="tool-actions"><a class="button tool-button" href="/scores/contact/">查看联系与查阅方式</a><a class="button tool-button tool-secondary" href="/scores/orchestras/submit/">提交高校乐团介绍</a></div><p>乐团收录请使用专门投稿页；下面的表单用于校谱、试奏和制谱需求。</p></section>'''


def access_notice(work='', version=''):
    query = urlencode({k: v for k, v in {'intent': 'score', 'work': work, 'version': version}.items() if v})
    return f'''<section class="shell score-access-section" aria-labelledby="score-access-title"><div class="score-access-notice">
    <div><p class="eyebrow">查阅前，先确认版本与使用范围</p><h2 id="score-access-title">乐谱正文暂不公开，查阅需要密码</h2><p>因版权与使用范围限制，专业谱库的 PDF 采用打开密码保护。如需查阅，请通过微信、QQ 或邮箱联系维护者，说明曲目、版本、所属乐团与用途。</p><p class="community-small">页面可公开浏览目录与声部信息。获取密码后，仍请按确认的使用范围取用资料；免费谱库按各原站许可提供入口。</p></div>
    <div class="actions"><a class="button primary" href="/scores/contact/?{e(query)}#request">联系获取查阅方式</a><a class="button" href="/scores/contact/#wechat">加微信 / QQ</a></div></div></section>'''


def support_strip():
    return '''<section class="shell"><div class="community-support-strip"><div><p class="eyebrow">让整理与分享继续</p><h2>一起把国乐谱汇留在这里</h2><p>一条勘误、一份乐团故事，或一次自愿打赏，都是对持续维护的支持。</p></div><div class="actions"><a class="button" href="/scores/contact/">联系维护者</a><a class="button primary" href="/scores/support/">支持这个站点</a></div></div></section>'''


def field(label, name, *, required=False, rows=0, maximum=200, placeholder='', kind='text'):
    attrs = f'name="{e(name)}" maxlength="{maximum}"' + (' required' if required else '')
    prompt = f' placeholder="{e(placeholder)}"' if placeholder else ''
    element = f'<textarea {attrs} rows="{rows}"{prompt}></textarea>' if rows else f'<input type="{kind}" {attrs}{prompt}>'
    return f'<label class="community-field"><span>{e(label)}{(" <span class=community-required>必填</span>" if required else "")}</span>{element}</label>'


def draft_output():
    return '''<div class="community-draft" data-draft-result hidden><h3>核对草稿后，再选择发送方式</h3><label class="community-field"><span>可复制的资料草稿</span><textarea rows="13" readonly data-draft-text></textarea></label><div class="actions"><button type="button" class="button" data-copy-draft>复制草稿</button><button type="button" class="button" data-download-draft>下载 TXT 草稿</button><a class="button primary" data-draft-mail>在邮件应用中打开</a></div><p class="community-small" data-draft-mail-note></p></div><p class="community-status" data-draft-status role="status" aria-live="polite"></p>'''


def intake_body():
    intro_mail = mailto('国乐谱汇 · 高校乐团收录', '乐团名称：\n所属高校：\n国家或地区 / 城市：\n介绍与官方链接：\n图片图注与可公开范围：\n回复方式：\n\n请手动添加照片原图或网盘分享链接。')
    c = config()
    form = ''.join([
        field('乐团正式名称', '乐团名称', required=True, maximum=100, placeholder='例如：中国科学技术大学学生民族乐团'),
        field('所属高校', '所属高校', required=True, maximum=100),
        field('国家或地区 / 城市', '所在地区', required=True, maximum=100),
        field('成立时间与出处（可选）', '成立时间与出处', maximum=300),
        field('乐团介绍、声部与日常活动', '乐团介绍', required=True, rows=5, maximum=3000, placeholder='写下乐团特点、主要声部、排练、教学或音乐会。人数和届数请注明统计日期。'),
        field('官方主页、音乐会视频与资料出处', '公开入口与出处', required=True, rows=3, maximum=1600, placeholder='优先提供学校、乐团官方页面或公开演出链接；多个链接可分行填写。'),
        field('照片图注与材料清单', '照片与图注', rows=4, maximum=2000, placeholder='例如：照片01，2025年专场音乐会谢幕，摄影者XXX，可用于乐团介绍。图片请稍后在邮件或聊天中发送。'),
        field('文字、图片的来源与可公开范围', '来源与展示范围', required=True, rows=3, maximum=1400, placeholder='说明哪些文字、图片由乐团提供，是否可在本站公开展示，以及需要保留的署名。'),
        field('资料核对日期（可选）', '资料核对日期', kind='date'),
        field('供维护者回复的联系方式', '回复方式', required=True, maximum=200, placeholder='邮箱、微信或QQ；仅供此次投稿沟通'),
    ])
    return f'''<div class="community-page">
    <section class="community-hero"><div class="shell"><nav class="community-breadcrumb" aria-label="面包屑"><a href="/scores/">国乐谱汇</a><span>/</span><a href="/scores/orchestras/">高校乐团风采</a><span>/</span><span aria-current="page">乐团投稿</span></nav><p class="eyebrow">分享属于你们的校园声音</p><h1>把你们的乐团，<br>介绍给更多人。</h1><p class="community-lede">欢迎全球高校民族乐团投稿。把介绍、照片和演出入口发给我，核对后整理为乐团专页。已有完整资料，可以直接发送。</p><div class="actions"><a class="button primary" href="{e(intro_mail)}">将资料发送到邮箱</a><a class="button" href="/scores/contact/#wechat">加微信 / QQ 发资料</a><a href="#prepare">先整理投稿草稿</a></div><p class="community-small">收件人：<a href="mailto:{e(c['email'])}">{e(c['email'])}</a> · 主题建议：国乐谱汇＋乐团名称</p></div></section>
    <section class="shell"><div class="community-checklist"><article><h2>乐团介绍</h2><p>正式名称、所属高校、所在城市、声部与活动。可以附上成立时间的出处和介绍原文。</p></article><article><h2>真实照片</h2><p>建议精选 3–8 张演出、排练或校园照片，保留原图，逐张说明时间、内容、摄影署名与展示范围。</p></article><article><h2>后续入口</h2><p>官方主页、公开音乐会视频与适合展示的机构联系方式，让读者继续了解乐团。</p></article></div><div class="community-note"><p>文字和图片经核对后收录，必要时会联系你补充。私人回复方式只用于沟通；需要公开的机构联系渠道请另外注明。</p><p>图片不会随此表单上传。发送邮件时请手动添加附件，或附可访问的资料链接。</p></div></section>
    <section class="shell community-compose" id="prepare"><div><p class="eyebrow">整理后发送</p><h2>乐团收录资料草稿</h2><p>也可以<a href="/scores/orchestras/intake-template.txt" download>下载空白模板</a>，在自己的文档中填写。以下内容只在当前页面整理，不会自动提交或保存。</p></div><form class="community-form" data-community-draft="高校乐团收录" data-recipient="{e(c['email'])}"><fieldset disabled><legend class="sr-only">乐团收录资料</legend><div class="community-form-grid">{form}</div><label class="community-check"><input type="checkbox" name="来源确认" value="已说明文字与图片来源和可公开展示范围" required><span>我已说明文字与图片的来源和可公开展示范围，愿意配合后续资料核对。</span></label><button type="submit" class="button primary" data-draft-submit hidden>整理资料草稿</button><noscript><p>填写辅助工具需要 JavaScript。请下载模板，或使用上方邮箱、微信和 QQ 直接发送材料。</p></noscript></fieldset>{draft_output()}</form></section>
    <section class="shell"><div class="community-note"><h2>收录以后，也欢迎持续更新</h2><p>新增演出、照片更正或失效链接，都可以通过同一联系方式告知。收录是校园文化展示，页面不表示学校或乐团对本站的机构背书。</p><div class="actions"><a class="button" href="/scores/orchestras/ustc-nmou/">看看 NMOU 示例</a><a class="button" href="/scores/orchestras/">返回乐团目录</a></div></div></section></div>'''


def contact_body():
    c = config()
    return f'''<div class="community-page"><section class="community-hero"><div class="shell"><p class="eyebrow">国乐谱汇 · 联系与交流</p><h1>有谱子的事，<br>也有乐团的故事。</h1><p class="community-lede">我是杨书泰，国乐谱汇的维护者。查阅谱件、校谱反馈、乐团投稿与制谱交流，都可以从这里联系我。</p><div class="actions"><a class="button primary" href="#channels">查看联系方式</a><a class="button" href="/scores/orchestras/submit/">提交乐团介绍</a><a href="#request">整理谱件查阅需求</a></div></div></section>
    <section class="shell">{contact_cards()}</section>
    <section class="shell community-compose" id="request"><div><p class="eyebrow">先把需要说清楚</p><h2>谱件查阅与交流</h2><p>专业谱库的 PDF 需要打开密码。请说明曲名、版本与使用场景，我会据此核对可提供的资料及使用范围。</p><p>有校勘问题，可使用<a href="/scores/tools/cooperation/#feedback">校谱反馈工具</a>逐项记录乐章、小节和声部。</p><p class="community-small">此处生成可检查的草稿。点击邮件链接会打开你的邮件应用，需要由你完成发送；网站不会自动收到资料。</p></div><form class="community-form" data-community-draft="谱件查阅与交流" data-recipient="{e(c['email'])}"><fieldset disabled><legend class="sr-only">谱件查阅需求</legend><div class="community-form-grid">
    <label class="community-field"><span>交流类型</span><select name="交流类型"><option value="谱件查阅">谱件查阅 / 获取打开密码</option><option value="版本核对">版本核对 / 缺少分谱</option><option value="制谱交流">翻谱 / 编配交流</option><option value="资料更正">网站资料更正</option></select></label>
    {field('作品名称', '作品名称', required=True, maximum=120, placeholder='可从曲目详情页自动带入')}
    {field('谱件版本与声部（可选）', '谱件版本', maximum=240)}
    {field('所属高校或乐团（可选）', '所属乐团', maximum=120)}
    {field('使用场景与需要的资料', '用途与需求', required=True, rows=4, maximum=2000, placeholder='例如：校内排练，需要首调笛子分谱；写明计划时间及已有文件。')}
    {field('回复方式（可选）', '回复方式', maximum=200, placeholder='也可以直接通过发件邮箱回复')}
    </div><button type="submit" class="button primary" data-draft-submit hidden>整理联系草稿</button><noscript><p>请直接使用上方邮箱、微信或 QQ 联系。</p></noscript></fieldset>{draft_output()}</form></section>
    <section class="shell"><div class="community-faq"><h2>联系前常见的几个问题</h2><details><summary>文件下载后为什么仍要密码？</summary><p>目录、文件下载与 PDF 的打开权限是不同环节。专业谱库保留现有加密 PDF；需要查阅时，请联系维护者核对资料及使用范围。</p></details><details><summary>打赏以后会自动收到谱子或密码吗？</summary><p>打赏是对网站维护的自愿支持，不是谱件购买、演出授权或密码领取条件。如需谱子，请另行说明查阅需求。</p></details><details><summary>怎样补充乐团介绍或照片？</summary><p>打开<a href="/scores/orchestras/submit/">高校乐团投稿页</a>，直接发送现成资料或整理草稿。照片和附件需在邮件或聊天中手动添加。</p></details><details><summary>没有安装邮件应用怎么办？</summary><p>复制邮箱地址，在你常用的网页邮箱中新建邮件；也可以复制草稿，通过微信或 QQ 发送。</p></details></div></section></div>'''


def support_body():
    cards = []
    for name, key, recipient, cls in [('微信支付', 'wechat-support.jpg', '泰泰（**泰）', 'wechat'), ('支付宝', 'alipay-support.jpg', '**泰', 'alipay')]:
        cards.append(f'''<article class="community-payment-card {cls}"><header><p class="eyebrow">自愿打赏</p><h2>{name}</h2><p>收款信息：{e(recipient)}</p></header><figure>{qr_image(key, name + '打赏收款二维码，由站点维护者提供')}<figcaption>使用{name}扫码，付款前核对收款信息与金额。</figcaption></figure><div class="actions"><a class="button" href="/scores/community/{key}" target="_blank" rel="noopener noreferrer">查看收款码原图</a><a class="button" href="/scores/community/{key}" download>保存二维码</a></div></article>''')
    return f'''<div class="community-page"><section class="community-hero support-hero"><div class="shell"><p class="eyebrow">一份小小的支持</p><h1>让校园里的国乐，<br>多一个相遇的地方。</h1><p class="community-lede">如果国乐谱汇帮你少走了一些找谱的弯路，或让你认识了一支喜欢的乐团，欢迎自愿打赏，支持这个站点的整理与维护。</p><p>金额随心。分享、勘误和乐团投稿，也同样珍贵。</p><div class="actions"><a class="button primary" href="#support-codes">查看打赏方式</a><a class="button" href="/scores/orchestras/submit/">分享乐团故事</a></div></div></section>
    <section class="shell" id="support-codes" aria-label="自愿打赏二维码"><div class="community-payment-grid">{''.join(cards)}</div><div class="community-note"><h2>感谢支持，请按自己的意愿决定</h2><p>这是对站点维护者的自愿打赏，不是公益募捐或谱件订单；打赏不附带密码、谱件交付或演出授权。查阅资料请到<a href="/scores/contact/#request">联系页面</a>说明需求。</p><p>手机访问可保存原图，再在对应应用中识别。本站不读取支付结果，也不会向你索要支付密码、验证码或银行卡信息。</p></div></section>
    <section class="shell"><div class="community-checklist"><article><h2>一条具体勘误</h2><p>写下曲名、版本、声部和小节，让下一份谱更可靠。</p><a href="/scores/tools/cooperation/#feedback">整理校谱反馈</a></article><article><h2>一份真实记录</h2><p>分享排练、音乐会和校园日常，让更多乐团彼此看见。</p><a href="/scores/orchestras/submit/">提交乐团资料</a></article><article><h2>一个官方来源</h2><p>补充值得收藏的原站入口，说明谱种、版本与取用条件。</p><a href="/scores/contact/">联系维护者</a></article></div></section></div>'''


def build_community(api):
    watch = json.loads((ROOT / 'scores/data/version-watch.json').read_text(encoding='utf-8'))
    updates = []
    for record in watch['entries']:
        items = ''.join(f'<li>{e(item)}</li>' for item in record['details'])
        links = ''.join(f'<a class="button" href="{e(item["url"])}">{e(item["title"])}</a>' for item in record['workUrls'])
        updates.append(f'<li><p class="community-update-label">{e(record["statusLabel"])} · <time datetime="{e(record["date"])}">{e(record["date"])}</time></p><h2>{e(record["title"])}</h2><p class="eyebrow">{e(record["version"])}</p><p>{e(record["summary"])}</p><ul>{items}</ul><div class="actions">{links}</div><p class="community-small">记录依据：{e(record["sourceLabel"])}</p></li>')
    updates_body = '<div class="community-page">' + api.hero('谱件与资料更新', '版本有来历，更新有记录。', watch['scopeNote']) + '<section class="shell"><div class="community-note"><p>查谱请以曲目页当前列明的版本为准。修订候选稿完成复核并确认使用范围后，才会替换正式入口。</p><p><a href="/scores/library/">浏览已发布谱件</a> · <a href="/scores/contact/#request">询问版本与查阅方式</a></p></div><ol class="community-update-list">' + ''.join(updates) + '</ol></section></div>'
    for route, title, description, body in [
        ('/scores/contact/', '联系维护者 · 邮箱、微信与 QQ', '联系国乐谱汇维护者杨书泰：查询谱件查阅方式、反馈版本问题、提交高校乐团介绍与制谱需求。', contact_body()),
        ('/scores/orchestras/submit/', '高校乐团投稿 · 介绍、照片与音乐会资料', '提交高校民族乐团介绍、照片和演出入口。通过邮箱、微信或QQ发送，或在本机整理可核对的投稿草稿。', intake_body()),
        ('/scores/support/', '支持国乐谱汇 · 自愿打赏与共建', '通过微信支付或支付宝自愿支持国乐谱汇的资料整理与站点维护，也欢迎勘误、乐团投稿和谱源补充。', support_body()),
        ('/scores/updates/', '版本动态 · 已发布谱件与修订进度', '查看国乐谱汇已发布的简谱版本、正在复核的修订材料与新增官方谱源；区分制作进度、正式发布和排练验证。', updates_body),
    ]:
        schema = {'@context': 'https://schema.org', '@type': 'ContactPage' if route == '/scores/contact/' else 'WebPage', 'url': api.BASE + route, 'name': title, 'inLanguage': 'zh-CN', 'description': description}
        api.output(route, title, description, body, active='/scores/orchestras/' if '/orchestras/' in route else '', script=asset_url('community.js'), schema=schema)
