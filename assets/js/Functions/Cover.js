(function () {
  function escapeHtml(str) {
    return String(str)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  function getRandomSloganPair() {
    const slogans = [
      {
        en: 'Mathematics, music, and a life slowly taking shape.',
        zh: '玉树临风美少年，揽镜自顾夜不眠'
      },
      {
        en: 'Rigor, rhythm, and a little bit of tenderness.',
        zh: '玉树临风美少年，揽镜自顾夜不眠'
      }
    ];
    return slogans[Math.floor(Math.random() * slogans.length)];
  }

  function setRandomCoverBackground(coverEl) {
    if (!coverEl) return null;

    const basePath = './assets/images/';
    const covers = ['cover_1.jpg'];
    const chosen = covers[Math.floor(Math.random() * covers.length)];
    const src = `${basePath}${chosen}`;

    // 先显示 cover 容器本身；CSS 中的轻量占位背景会立刻出现。
    coverEl.classList.add('visible');
    coverEl.classList.remove('cover-bg-loaded', 'cover-bg-fallback');

    const reveal = () => {
      coverEl.style.setProperty('--cover-bg', `url("${src}")`);
      requestAnimationFrame(() => {
        coverEl.classList.add('cover-bg-loaded');
      });
    };

    const img = new Image();
    img.decoding = 'async';
    if ('fetchPriority' in img) img.fetchPriority = 'high';

    img.onload = () => {
      if (img.decode) {
        img.decode().catch(() => null).finally(reveal);
      } else {
        reveal();
      }
    };

    img.onerror = () => {
      console.warn(`[Cover] Failed to load ${src}; using placeholder background.`);
      coverEl.classList.add('cover-bg-fallback');
    };

    img.src = src;

    const idle = window.requestIdleCallback || ((callback) => window.setTimeout(callback, 800));
    idle(() => {
      covers
        .filter((name) => name !== chosen)
        .forEach((name) => {
          const preload = new Image();
          preload.decoding = 'async';
          preload.src = `${basePath}${name}`;
        });
    });

    return chosen;
  }

  const mount = document.getElementById('mount-cover') || document.body;
  const sloganPair = getRandomSloganPair();

  mount.insertAdjacentHTML(
    'beforeend',
    `
    <div id="cover">
      <div id="avatar-frame"
           data-cursor="precise_select"
           data-cursor-fallback="pointer">
        <img src="./assets/images/avatar.jpg" alt="Profile Avatar" loading="lazy">
      </div>

      <div id="name" data-name-en="Thomas" data-name-zh="泰泰">Thomas</div>
      <div id="slogan"
           data-slogan-en="${escapeHtml(sloganPair.en)}"
           data-slogan-zh="${escapeHtml(sloganPair.zh)}">${escapeHtml(sloganPair.en)}</div>

      <button id="cover-scroll"
              type="button"
              aria-label="Scroll to About"
              title="Scroll to About"
              data-cursor="precise_select"
              data-cursor-fallback="pointer">
        <svg viewBox="0 0 64 64" aria-hidden="true" focusable="false">
          <path class="chev c1" d="M14 22 L32 40 L50 22" />
          <path class="chev c2" d="M18 30 L32 44 L46 30" />
          <path class="chev c3" d="M22 38 L32 48 L42 38" />
        </svg>
        <span class="cover-scroll-sub" data-cover-scroll-en="Scroll" data-cover-scroll-zh="进入">Scroll</span>
      </button>
    </div>
    `
  );

  const coverEl = document.getElementById('cover');
  setRandomCoverBackground(coverEl);

  (function initCoverArrowStardust() {
    const arrow = document.getElementById('cover-scroll');
    if (!arrow) return;
    let stardustTimer = null;
    function spawnStardust() {
      const dust = document.createElement('span');
      dust.className = 'cover-stardust';
      const x = (Math.random() - 0.5) * 24;
      const duration = 1200 + Math.random() * 800;
      dust.style.setProperty('--x', `${x}px`);
      dust.style.animationDuration = `${duration}ms`;
      arrow.appendChild(dust);
      dust.addEventListener('animationend', () => dust.remove());
    }
    function startStardust() {
      if (stardustTimer) return;
      stardustTimer = setInterval(spawnStardust, 140);
    }
    function stopStardust() {
      if (!stardustTimer) return;
      clearInterval(stardustTimer);
      stardustTimer = null;
    }
    arrow.addEventListener('mouseenter', startStardust);
    arrow.addEventListener('mouseleave', stopStardust);
    arrow.addEventListener('focus', startStardust);
    arrow.addEventListener('blur', stopStardust);
  })();
})();
