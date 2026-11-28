import { profiles, roles } from './instruments.mjs';
import { readRange } from './musicxml.mjs';

export const projectKind = 'guoyue-arrange-project';
export const projectVersion = 1;
export const projectSizeLimit = 250000;
const maxSeats = 64;
const maxSeatId = 1000000000;
const own = (object, key) => Object.hasOwn(object, key);
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const hashPattern = /^[a-f0-9]{64}$/;

/** Fingerprint decoded XML, so the same XML in an MXL container has the same identity. */
export async function scoreFingerprint(xml) {
  if (typeof xml !== 'string' || !xml.trim()) throw new Error('原谱内容为空，无法生成谱件指纹。');
  if (!globalThis.crypto?.subtle) throw new Error('当前浏览器无法生成谱件指纹，请使用 HTTPS 或本机预览地址。');
  const digest = await globalThis.crypto.subtle.digest('SHA-256', new TextEncoder().encode(xml));
  return [...new Uint8Array(digest)].map(byte => byte.toString(16).padStart(2, '0')).join('');
}

function validText(value, maximum) {
  return typeof value === 'string' && value.length > 0 && value.length <= maximum;
}

function seatsFrom(rows) {
  if (!Array.isArray(rows) || rows.length > maxSeats) throw new Error('项目最多支持 64 个演奏席位。');
  const seen = new Set();
  return rows.map(row => {
    if (!object(row) || !Number.isSafeInteger(row.id) || row.id < 1 || row.id > maxSeatId || seen.has(row.id)) {
      throw new Error('项目中的席位编号缺失、重复或无效。');
    }
    seen.add(row.id);
    if (!own(profiles, row.profile) || !own(roles, row.role)) throw new Error('项目含有无法识别的乐器或声部作用。');
    if (!validText(row.low, 16) || !validText(row.high, 16)) throw new Error('席位音域须填写音名或 MIDI 音高。');
    const low = readRange(row.low), high = readRange(row.high);
    if (low === null || high === null || low > high) throw new Error(`席位 ${row.id} 的音域无效，修正后再保存项目。`);
    // Only these editable settings can be restored. Solver output is never trusted.
    return { id: row.id, profile: row.profile, role: row.role, low: row.low.trim(), high: row.high.trim() };
  });
}

function partsFrom(rows) {
  if (!Array.isArray(rows) || !rows.length || rows.length > 64) throw new Error('项目须包含 1 至 64 个原谱声部。');
  const seen = new Set();
  return rows.map(row => {
    if (!object(row) || !validText(row.id, 256) || seen.has(row.id)) throw new Error('项目中的原声部编号缺失、重复或无效。');
    seen.add(row.id);
    if (!own(roles, row.role) || !['required', 'optional'].includes(row.priority)) throw new Error('项目含有无法识别的声部作用或优先级。');
    return { id: row.id, role: row.role, priority: row.priority };
  });
}

function validateProject(data) {
  if (!object(data) || data.kind !== projectKind || data.version !== projectVersion) {
    throw new Error('请选择整曲工作台导出的「项目设置」JSON。结果报告或分段设置不能作为整曲项目导入。');
  }
  if (!object(data.source) || !hashPattern.test(data.source.sha256 ?? '')) throw new Error('项目缺少有效的谱件指纹，无法安全恢复。');
  if (typeof data.source.title !== 'string' || data.source.title.length > 500) throw new Error('项目曲名无效。');
  const seats = seatsFrom(data.seats), parts = partsFrom(data.parts);
  const maximum = Math.max(0, ...seats.map(seat => seat.id));
  if (!Number.isSafeInteger(data.lastSeatId) || data.lastSeatId < maximum || data.lastSeatId > maxSeatId) {
    throw new Error('项目的席位编号计数无效。');
  }
  return {
    kind: projectKind, version: projectVersion,
    source: { sha256: data.source.sha256, title: data.source.title },
    lastSeatId: data.lastSeatId, parts, seats,
  };
}

export function createProject({ scoreKey, title, parts, seats, lastSeatId }) {
  return validateProject({
    kind: projectKind, version: projectVersion,
    source: { sha256: scoreKey, title: String(title ?? '').slice(0, 500) },
    parts, seats, lastSeatId,
  });
}

export function readProject(text) {
  if (typeof text !== 'string' || new TextEncoder().encode(text).length > projectSizeLimit) throw new Error('项目文件过大，请选择 250 KB 以内的设置文件。');
  let data;
  try { data = JSON.parse(text); } catch { throw new Error('项目文件不是有效的 JSON。'); }
  return validateProject(data);
}

/** No state is changed until both the original XML and its part IDs match. */
export function restoreProject(project, scoreKey, currentParts) {
  const clean = validateProject(project);
  if (!hashPattern.test(scoreKey ?? '') || clean.source.sha256 !== scoreKey) {
    throw new Error('项目与当前原谱的指纹不一致。请载入原来的 MusicXML/MXL；当前设置保持不变。');
  }
  if (!Array.isArray(currentParts) || currentParts.length !== clean.parts.length) throw new Error('项目的声部清单与当前读谱结果不一致，请重新核对源文件。');
  const settings = new Map(clean.parts.map(part => [part.id, part]));
  const currentIds = new Set(currentParts.map(part => part.id));
  if (currentIds.size !== currentParts.length || currentParts.some(part => !settings.has(part.id))) {
    throw new Error('项目的原声部编号与当前读谱结果不一致，请重新核对源文件。');
  }
  return {
    parts: currentParts.map(part => ({ ...part, ...settings.get(part.id) })),
    seats: clean.seats.map(seat => ({ ...seat })),
    lastSeatId: clean.lastSeatId,
  };
}
