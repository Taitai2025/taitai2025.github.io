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
3. If you want to change **visual style**, edit the corresponding file under `assets/css`.
4. To enable **real analytics**, replace the placeholder IDs inside `assets/js/Functions/Social.js`.
