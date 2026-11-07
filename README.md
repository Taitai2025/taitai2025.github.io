# 杨书泰 Shutai Yang · 个人主页

2026-11-07 更新。网站可直接由静态服务器或 GitHub Pages 托管。只发布本文件所在的网站目录，不要上传上一级的申请材料与工作说明。

## 搜索收录与内容更新

个人简介、科研和随记提供 `/about/`、`/research/`、`/notes/` 三个独立入口，保留原有 `#resume` 等链接兼容。正文已预先写入 HTML，搜索引擎无需执行脚本即可读取；浏览器继续保留原有封面、主题、语言切换和阅读器交互。`robots.txt` 允许抓取，`sitemap.xml` 列出四个公开页面，每页包含对应标题、摘要、规范网址和结构化资料。

修改下方内容文件后，运行 `npm install`（首次）及 `npm run build`，重新生成首页和三个独立页面，再发布整个网站目录。`node_modules/` 无需发布。只修改生成页面会在下次构建时被覆盖。维护环境也可直接运行 `node scripts/build-static.cjs`，前提是已安装 `jsdom`。

生成站点地图和可抓取正文有助于发现和理解页面，但不保证搜索引擎立即收录。实际索引状态应在站长账户的 Google Search Console / Bing Webmaster Tools 中查看；拥有者验证完成后可提交站点地图和请求重新抓取。

音乐改编作品的网页仅公开文字介绍；《大东北我的家乡》和《La La Land》的乐谱、分谱、工程文件、试听音频及压缩包属于未公开销售材料，不应加入网站目录或 Git 提交。

## 本轮入口与维护位置

- 默认打开动态封面 `#cover`；`#resume`、`#research`、`#schedule`、`#social`、`#toolkit`、`#meditations`可直接分享并进入对应正文。
- 个人介绍、完整履历、荣誉、音乐与任职：`assets/js/Content/ZH/resume_ZH.js`及`EN/resume_EN.js`。两种语言同步修改。
- 论文、文章、报告：`assets/js/Content/research.js`中的`window.RESEARCH_CONTENT`。条目区分预印本/在投/正式文章，PDF为公开版本。
- 科研渲染、资源链接与履历目录：`assets/js/Functions/Research.js`。
- 当前视觉层：`assets/stardust/style/stardust.css` 聚合源站基础、字体、导航、简介、社交、日程与随记样式；本站结构适配放在同目录 `adaptation.css`。旧 `assets/css/academic.css` 保留但已停止加载，后续视觉修改从 Stardust 层继续。
- 动态封面、景深、进入与滚轮交互：`assets/stardust/cover/`；数学加载动画：`assets/stardust/loading/`；光标：`assets/stardust/Custom-cursors.js` 与 `cursors/`。背景图和视频在对应 `images/cover/`、`animation/cover/`；不改动旧照片。
- 邮箱展开/复制和页脚：`assets/stardust/profile/`。ORCID `0009-0003-5581-2970`、GitHub `Taitai2025` 和 AMSS 官网已接入简介、社交与页脚。
- PDF方式沿用源站：`assets/stardust/resources/PdfReader.js`、`ResourceLinks.js` 与对应CSS连接到 `assets/vendor/pdfjs/`。普通点击页内阅读，可全屏、新标签、下载或直接打开原文件；直接双击本地HTML时回退为原生PDF打开，完整阅读器请通过HTTP预览。
- 导航路由：`assets/js/Functions/Bootstrap.js`；中英导航：`Top-nav.js`及`Translate.js`。
- 公开附件：`assets/documents/`，证书在其`honors/`子目录。附件来源与公开处理记录在上一级`工作说明/research-attachments.md`。
- 原有封面、工具、社交、日程、随记、完整课程与经历均保留。旧暑假节律与旧焕新计划已标历史语境。
- `README.markdown`和`assets/pdf/`的两份旧PDF属于参考模板作者，不代表杨书泰的履历或成果。保留其信息与署名，不加入本人论文列表。`LICENSE`中原作者署名保留。
- `assets/js/Functions/Blog.js`保留了原模板的独有彩蛋代码，目前未由首页加载；本轮没有擅自启用或删去。

## 2026-11-07 扩展内容与验收

现有公开附件69份PDF，共957页；其中包含科研、学位论文、课程、音乐文章、教学资料、荣誉证据和个人文稿，不能将全部附件称为获奖证书。活动整理为80组，保留具体日期、作品和参与工作；17项岗位保留，其中12项补充了有来源的职责描述。57张活动照片分为舞台、教学、排练和组织交流四组，并关联相关活动。

本轮已核验桌面与390px手机版式、活动深链接、语言切换、相册和真实PDF渲染。25项DOM检查、四个静态入口检查及双语扩展内容/附件哈希检查通过。公开副本单独处理，私人源文件不随网站发布。完整来源、公开处理与待补证明记录保存在外层工作说明目录。

## 检查与发布

浏览器中检查中英切换、六个导航页、深浅主题、工具搜索、日程便签与PDF阅读/下载。根目录`工作说明/checks/verify-site.cjs`为维护时的DOM集成检查，不属于网站部署内容。
本轮25项DOM检查通过，覆盖页面、中英文、科研与附件、主题和基础工具；36个网站及迁移脚本语法检查通过。浏览器已实际检查桌面简介、科研、51页PDF渲染和全屏，并修复全屏导航遮挡及外边距；390px手机等实机检查的最终记录以外层 `工作说明/Stardust风格改造完成说明.md` 为准，不能把本说明理解为所有设备和全部交互均已验收。所有先前新生成/脱敏PDF已经渲染核查。以上为 2026-10-23 的历史验收记录；后续发布情况以 GitHub Pages 部署记录为准。

以下保留原有模块说明，供理解各模块原始职责；涉及首屏、科研和附件的内容以上方更新说明为准。

---

# Taitai Homepage (Stardust-style modular rebuild)

This rebuild follows the **same modular planning philosophy** as the Stardust homepage:
content is separated into JS modules, styles are split into CSS files, and page behaviors are handled by function scripts.

## Quick structure guide

### Root
- `index.html`  
  Main entry file. It only keeps the global skeleton and mounts each page module.

### assets/css
- `main.css`  
  Global theme, paper-like layout, resume typography, shared section styles.
- `top-nav.css`  
  Fixed top navigation bar, language switch, theme button, clock, back button.
- `cover.css`  
  Full-screen cover page, avatar, title, scroll arrow, entrance effects.
- `social.css`  
  Social cards and website statistics section.
- `toolkit.css`  
  Searchable / filterable toolkit page layout.
- `schedule.css`  
  Current Rhythm page, switcher buttons, note box, placeholder panels.
- `meditations.css`  
  Notes / Meditations page layout.
- `blog.css`  
  Reserved blog / easter-egg stylesheet, kept for Stardust-style structure.
- `cursor.css`  
  Reserved file; actual cursor logic is handled by JS.

### assets/js/Functions
- `Top-nav.js`  
  Renders and controls the fixed navigation bar.
- `Cover.js`  
  Renders the cover page, rotating cover backgrounds, scroll arrow effect.
- `Bootstrap.js`  
  Controls page switching between cover and inner pages.
- `Clock.js`  
  Updates the clock shown on page controls.
- `Theme.js`  
  Light / dark theme toggle logic.
- `Translate.js`  
  English / Chinese switching logic.
- `Custom-cursors.js`  
  Applies the Stardust-style cursor system.
- `Expanders.js`  
  Handles expandable content blocks.
- `Social.js`  
  Renders your social cards and the statistics placeholder area.
- `Toolkit.js`  
  Renders the toolkit page and its search / filter interactions.
- `Schedule.js`  
  Controls the Current Rhythm page tabs and the local note box.

### assets/js/Content/EN
- `resume_EN.js`  
  English content for the About / Resume page.
- `social_EN.js`  
  English labels for the Social page.
- `toolkit_EN.js`  
  English labels for the Toolkit page.
- `schedule_EN.js`  
  English text for the Current Rhythm page and its mount structure.
- `meditations_EN.js`  
  English content for the Notes page.

### assets/js/Content/ZH
- `resume_ZH.js`  
  Chinese content for the About / Resume page.
- `social_ZH.js`  
  Chinese labels for the Social page.
- `toolkit_ZH.js`  
  Chinese labels for the Toolkit page.
- `schedule_ZH.js`  
  Chinese text for the Current Rhythm page.
- `meditations_ZH.js`  
  Chinese content for the Notes page.

### assets/images
Replace these directly with your own files when ready:
- `avatar.jpg` — cover avatar
- `profile.jpg` — About page photo
- `cover_1.jpg` ~ `cover_6.jpg` — rotating cover backgrounds
- `favicon.png` — site icon

### assets/pdf
Reserved for future PDF materials such as certificates, slides, posters, CVs, or music scores.

### assets/cursors / assets/fonts / assets/animation / assets/audio
These keep the visual and interaction style close to Stardust's modular arrangement.

## Notes for future editing
1. If you want to change **text content**, edit the files under `assets/js/Content/EN` and `assets/js/Content/ZH`.
2. If you want to change **page structure / interaction**, edit the corresponding file under `assets/js/Functions`.
3. If you want to change **visual style**, continue in `assets/stardust/style/` (especially `adaptation.css`); the older `assets/css` files below describe retained historical modules and are not the current visual source of truth.
4. To enable **real analytics**, replace the placeholder IDs inside `assets/js/Functions/Social.js`.
