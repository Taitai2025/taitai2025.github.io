(function () {
  const mount = document.getElementById("mount-meditations") || document.body;
  mount.insertAdjacentHTML("beforeend", `
  <div id="meditations">
    <button id="toggle-btn-meditations">
      <span><i class="fas fa-sun"></i></span>
    </button>
    <div id="clock-meditations">GMT+8 00:00</div>
    <div class="container">
      
<div class="resume-heading">Notes</div>
<div class="medit-contents-title">
  <span class="medit-contents-title-text">Fragments &amp; Placeholders</span>
</div>

<div class="medit-entry medit-big">
  <div class="medit-row medit-row-big">
    <button class="expander" data-expand-target="medit-notes-site" data-expand-key="medit-notes-site" aria-label="Expand section"></button>
    <span class="medit-title">About this page</span>
  </div>
  <div class="expand-row medit-expand" id="medit-notes-site" aria-hidden="true" style="display:none;">
    <div class="medit-body">
      <p>This page is intentionally light. I keep it here mainly as a reserved place for research notes, music reflections, travel fragments, and other longer-form writing I may want to organize later.</p>
      <p>In this rebuild, its role is also structural: the page stays in the same position and file layout as the Stardust site, so later additions can be made without touching the overall architecture.</p>
    </div>
  </div>
</div>

<div class="medit-entry">
  <div class="medit-row medit-row-small">
    <button class="expander" data-expand-target="medit-research" data-expand-key="medit-research" aria-label="Expand section"></button>
    <span class="medit-title">Research notes (reserved)</span>
  </div>
  <div class="expand-row medit-expand" id="medit-research" aria-hidden="true" style="display:none;">
    <div class="medit-body">
      <p class="medit-empty">A place for optimization ideas, reading notes, and fragments from ongoing work.</p>
    </div>
  </div>
</div>

<div class="medit-entry">
  <div class="medit-row medit-row-small">
    <button class="expander" data-expand-target="medit-music" data-expand-key="medit-music" aria-label="Expand section"></button>
    <span class="medit-title">Music notes (reserved)</span>
  </div>
  <div class="expand-row medit-expand" id="medit-music" aria-hidden="true" style="display:none;">
    <div class="medit-body">
      <p class="medit-empty">A place for arrangement drafts, rehearsal memories, and small reflections related to the orchestra.</p>
    </div>
  </div>
</div>

    </div>
  </div>
`);
})();
