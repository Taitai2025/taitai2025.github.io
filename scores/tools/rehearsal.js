'use strict';
const KEY = 'guoyue:rehearsal-checklist:v1';
const checkboxes = [...document.querySelectorAll('#rehearsal-checklist input[type="checkbox"]')];
const status = document.getElementById('checklist-count');
try {
  const previous = JSON.parse(localStorage.getItem(KEY) || '[]');
  if (Array.isArray(previous)) for (const entry of checkboxes) entry.checked = previous.includes(entry.name);
} catch {
  /* Keep the checklist usable without storage. */
}
function update() {
  const completed = checkboxes.filter(item => item.checked).map(item => item.name);
  status.textContent = `本次勾选 ${completed.length} / ${checkboxes.length} 项。勾选仅记录在此浏览器。`;
  try { localStorage.setItem(KEY,JSON.stringify(completed)); }
  catch { /* Keep the checklist usable without storage. */ }
}
for (const entry of checkboxes) entry.addEventListener('change',update);
document.getElementById('print-checklist').addEventListener('click',() => window.print());
document.getElementById('reset-checklist').addEventListener('click',() => {
  for (const entry of checkboxes) entry.checked = false;
  update();
});
update();
