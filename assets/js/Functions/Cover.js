(function () {
  function getRandomSlogan() {
    const slogans = [
      'Mathematics, music, and a life slowly taking shape.',
      '在数学、音乐与日常之间，慢慢把自己活成一条清晰的轨迹。',
      'Rigor, rhythm, and a little bit of tenderness.',
      '把理性、审美与行动力，安放在同一条成长轨迹里。'
    ];
    return slogans[Math.floor(Math.random() * slogans.length)];
  }

  function setRandomCoverBackground(coverEl) {
    if (!coverEl) return null;
    const covers = ['cover_1.jpg','cover_2.jpg','cover_3.jpg','cover_4.jpg','cover_5.jpg','cover_6.jpg'];
    const chosen = covers[Math.floor(Math.random() * covers.length)];
    coverEl.style.backgroundImage = `url('./assets/images/${chosen}')`;
    coverEl.style.backgroundRepeat = 'no-repeat';
    coverEl.style.backgroundPosition = 'center center';
    coverEl.style.backgroundSize = 'cover';
    coverEl.classList.add('visible');
    return chosen;
  }

  const mount = document.getElementById("mount-cover") || document.body;
  const slogan = getRandomSlogan();

  mount.insertAdjacentHTML(
    "beforeend",
    `
    <div id="cover">
      <div id="avatar-frame"
           data-cursor="precise_select"
           data-cursor-fallback="pointer">
        <img src="./assets/images/avatar.jpg" alt="Profile Avatar" loading="lazy">
      </div>

      <div id="name">Thomas · TaiTai</div>
      <div id="slogan">${slogan}</div>

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
        <span class="cover-scroll-sub">Scroll</span>
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
