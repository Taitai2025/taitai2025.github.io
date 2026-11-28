'use strict';

const CONTACT = 'taitai@mail.ustc.edu.cn';
const contextParams = new URLSearchParams(location.search);
const contextWork = (contextParams.get('work') || '').slice(0, 80);
const contextVersion = (contextParams.get('version') || '').slice(0, 100);
const scoreField = document.querySelector('[data-draft="校谱反馈"] [name="谱件版本"]');
if (scoreField && !scoreField.value && contextWork) {
  scoreField.value = [contextWork, contextVersion].filter(Boolean).join(' · ').slice(0, scoreField.maxLength);
}
for (const form of document.querySelectorAll('[data-draft]')) {
  const preview = form.querySelector('.generated-draft');
  const status = form.querySelector('output');
  const actions = form.querySelector('[data-ready]');
  const letter = form.querySelector('[data-mail]');
  const save = form.querySelector('[data-save]');
  const title = form.dataset.draft;
  let body = '';
  function draftParts(data) {
    return [...data].filter(([,value]) => String(value).trim()).map(([key,value]) => [key,String(value).trim()]);
  }
  function draftBody(entries) {
    return [`国乐谱汇 · ${title}`,...entries.map(([key,value]) => `${key}\n${value}`)].join('\n\n');
  }
  form.addEventListener('submit',event => {
    event.preventDefault();
    body = draftBody(draftParts(new FormData(form)));
    preview.textContent = body;
    preview.hidden = false;
    actions.hidden = false;
    const url = `mailto:${CONTACT}?subject=${encodeURIComponent('国乐谱汇 · ' + title)}&body=${encodeURIComponent(body)}`;
    if (url.length < 1850) {
      letter.href=url;
      letter.hidden=false;
      status.textContent='草稿已生成。可以下载，也可在自己的邮件应用中打开。';
    } else {
      letter.removeAttribute('href');
      letter.hidden=true;
      status.textContent='草稿已生成。内容较长，请下载后粘贴到邮件中。';
    }
  });
  form.addEventListener('input', () => {
    if (!body) return;
    body='';
    preview.textContent='';
    preview.hidden=true;
    actions.hidden=true;
    letter.removeAttribute('href');
    status.textContent='内容已修改。请重新生成草稿。';
  });
  save.addEventListener('click', () => {
    if (!body) return;
    const url = URL.createObjectURL(new Blob([body+'\n'], {type:'text/plain;charset=utf-8'}));
    const link=document.createElement('a');
    link.href=url;
    link.download=`国乐谱汇_${title}.txt`;
    link.click();
    window.setTimeout(() => URL.revokeObjectURL(url),1000);
  });
}
