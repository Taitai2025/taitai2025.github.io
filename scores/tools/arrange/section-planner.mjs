import { solveAssignment } from './assignment.mjs';
import { evaluateMapping } from './musicxml.mjs';

const EPS = 1e-8;
const profileId = (target) => target?.profile ?? target?.name;
const near = (left, right) => Number.isFinite(left) && Number.isFinite(right) && Math.abs(left - right) < EPS;
const pitchesKey = (event) => JSON.stringify([event.staff, event.voice, event.pitchKey ?? event.sounding ?? null]);
const sounds = (event) => !event.cue && !event.rest && event.type !== 'rest';

const limitations = [
  '按总谱书面小节顺序逐段求解。每位演奏员每段最多负责一个声部，各段结果沿用前段安排。',
  '跨段延音优先沿用同一演奏员和乐器。可选延音若影响下一段必保声部的覆盖，会标记供复核。',
  '换乐器休止使用总谱的四分音符拍。实际演奏速度、反复和跳转的走向须在排练中复核。',
  '音域及复音检查基于已读谱面和名单设置。编制仍须核对实奏能力、音色和记谱，尤其是标有待复核的安排。',
];

export const sectionGapReasons = {
  'no-player': '名单中没有演奏员',
  'unavailable': '本段有缺席小节',
  'incompatible': '登记乐器未通过实音、复音或谱表检查',
  'switch-rest': '换乐器休止不足',
  'switch-timing': '换乐器的发音或结束拍位还需核对',
  'player-conflict': '合适的演奏员已分配其他声部',
  'tie-uncovered': '跨段延音没有可延续的演奏员与乐器',
  'tie-notation': '相邻两段的延音记号需核查',
  'optional-layer-omitted': '比较候选中整条可选声部不分配，请由编配者确认取舍',
};

function sectionRanges(measures, supplied) {
  const rehearsalStarts = measures.flatMap((measure, index) => index > 0 && measure.rehearsals?.length ? [index] : []);
  const starts = [0, ...rehearsalStarts, measures.length];
  const sections = supplied ?? starts.slice(0, -1).map((start, index) => ({ start, end: starts[index + 1] }));
  let expectedStart = 0;
  for (const { start, end } of sections) {
    if (start !== expectedStart || !Number.isInteger(end) || end <= start || end > measures.length) {
      throw new Error('分段须连续覆盖总谱，每段至少有一个小节。');
    }
    expectedStart = end;
  }
  if (expectedStart !== measures.length) throw new Error('分段须覆盖到总谱最后一个小节。');
  return sections;
}

function validateRoster(players, measureCount) {
  const ids = new Set();
  for (const player of players) {
    if (player.id === null || player.id === undefined || player.id === '' || ids.has(player.id)) {
      throw new Error('每位演奏员须有唯一编号。');
    }
    ids.add(player.id);
    for (const { start, end } of player.unavailable ?? []) {
      if (!Number.isInteger(start) || !Number.isInteger(end) || start < 0 || end <= start || end > measureCount) {
        throw new Error('缺席区间须对应总谱中的连续小节。');
      }
    }
  }
}

function peakPolyphony(notes) {
  const changes = notes.flatMap(({ startQ, endQ, grace }) =>
    !grace && endQ - startQ > EPS ? [[startQ, 1], [endQ, -1]] : []);
  changes.sort((left, right) => near(left[0], right[0]) ? left[1] - right[1] : left[0] - right[0]);
  let active = 0;
  let peak = 0;
  for (const [, change] of changes) {
    active += change;
    peak = Math.max(peak, active);
  }
  return peak;
}

function demandFor(part, section, ongoing) {
  const { start, end, startQ, endQ } = section;
  const continued = ongoing.filter(({ endQ }) => endQ > startQ + EPS);
  const events = [...continued, ...part.measureDetails.slice(start, end).flatMap(({ events }) => events.filter(sounds))];
  if (!events.length) return null;
  const pitched = events.filter((event) => event.type === 'pitched' && Number.isFinite(event.sounding));
  const unpitched = events.filter((event) => event.type === 'unpitched').length;
  const bounds = pitched.length ? pitched.reduce(([low, high], { sounding }) => [Math.min(low, sounding), Math.max(high, sounding)], [Infinity, -Infinity]) : null;
  const offsets = new Map();
  for (const event of pitched) {
    const shift = event.transpose ?? part.shift;
    if (shift) offsets.set(`${shift.chromatic}/${shift.diatonic}`, shift);
  }
  const type = pitched.length && unpitched ? 'mixed' : pitched.length ? 'pitched' : unpitched ? 'unpitched' : 'unknown';
  const shift = offsets.size === 1 ? offsets.values().next().value : null;
  const polyphony = peakPolyphony(pitched.filter((event) => Number.isFinite(event.endQ)).map(({ startQ: onset, endQ: release, grace }) => ({
    startQ: Math.max(startQ, onset), endQ: Math.min(endQ, release), grace,
  })));
  const source = { id: part.id, name: part.name, priority: part.priority ?? 'required', role: part.role ?? 'any', bounds, shift, polyphony };
  const compatibility = {
    ...part, ...source, type,
    ambiguousPitch: events.length - pitched.length - unpitched,
    noteEvents: events,
    keyChanges: [...new Set(events.map(({ fifths }) => fifths ?? 0))],
    voices: new Set(events.map(({ voice }) => voice)).size,
  };
  const ongoingOut = events.filter(({ endQ: release }) => release > endQ + EPS);
  const incoming = events.filter((event) => continued.includes(event) || event.tieStop && near(event.startQ, startQ));
  const outgoing = events.filter((event) => event.endQ > endQ + EPS || event.tieStart && near(event.endQ, endQ));
  let firstAttackQ = Infinity;
  let lastReleaseQ = -Infinity;
  for (const event of events) {
    if (!event.tieStop && !continued.includes(event) && Number.isFinite(event.startQ)) firstAttackQ = Math.min(firstAttackQ, event.startQ);
    if (!Number.isFinite(event.endQ)) lastReleaseQ = NaN;
    else lastReleaseQ = Math.max(lastReleaseQ, event.endQ);
  }
  const uncertainAttack = events.some((event) => (event.grace || event.performanceModified) && near(event.startQ, firstAttackQ));
  const uncertainRelease = events.some((event) => event.letRing ||
    (event.grace || event.performanceModified || event.fermata) && near(event.endQ, lastReleaseQ));
  return {
    source, compatibility, ongoingOut, incoming, outgoing, uncertainAttack, uncertainRelease,
    firstAttackQ: Number.isFinite(firstAttackQ) ? firstAttackQ : null,
    lastReleaseQ: Number.isFinite(lastReleaseQ) ? lastReleaseQ : null,
  };
}

function tieAgrees(before, demand) {
  if (before?.outgoing.length !== demand.incoming.length) return false;
  const expected = before.outgoing.map(pitchesKey).sort();
  return demand.incoming.map(pitchesKey).sort().every((key, index) => key === expected[index]);
}

function available(player, { start, end }) {
  return !(player.unavailable ?? []).some((range) => range.start < end && range.end > start);
}

function switchWindow(model, previous, demand, minimumBeats) {
  const releaseQ = previous.lastReleaseQ;
  const attackQ = demand.firstAttackQ;
  if (!Number.isFinite(releaseQ) || !Number.isFinite(attackQ) || previous.uncertainRelease || demand.uncertainAttack) {
    return { reason: 'switch-timing' };
  }
  const availableBeats = attackQ - releaseQ;
  if (availableBeats < -EPS) return { reason: 'switch-rest' };
  if (model.measures.some((measure) => measure.uncertain && measure.startQ <= attackQ + EPS && measure.endQ >= releaseQ - EPS)
    || (model.timingUncertainties ?? []).some(({ kind, atQ, endQ }) =>
      ['rhythm', 'played-timing'].includes(kind) && (endQ ?? atQ) >= releaseQ - EPS && atQ <= attackQ + EPS)) {
    return { reason: 'switch-timing' };
  }
  if (availableBeats + EPS < minimumBeats) return { reason: 'switch-rest' };
  return { availableBeats: Math.max(0, availableBeats), minimumBeats, releaseQ, attackQ, allowed: true };
}

function playerCandidate(model, player, demand, previous, switchBeats, reasons) {
  if (!available(player, demand.section)) {
    reasons.add('unavailable');
    return null;
  }
  let best = null;
  for (const target of player.instruments ?? []) {
    const evaluation = evaluateMapping(demand.compatibility, target, demand.source.role);
    if (evaluation.cost === null) {
      reasons.add('incompatible');
      continue;
    }
    const changingInstrument = previous && profileId(previous.target) !== profileId(target);
    const time = changingInstrument ? switchWindow(model, previous, demand, switchBeats) : null;
    if (time?.reason) {
      reasons.add(time.reason);
      continue;
    }
    const continuityCost = changingInstrument ? 2 : previous && previous.source.id !== demand.source.id ? 1 : 0;
    if (!best || evaluation.cost < best.evaluation.cost || (evaluation.cost === best.evaluation.cost && continuityCost < best.continuityCost)) {
      const sw = time ? { player, from: previous.target, to: target, fromSource: previous.source, toSource: demand.source, ...time } : null;
      best = { player, target, evaluation, continuityCost, sw };
    }
  }
  if (!player.instruments?.length) reasons.add('incompatible');
  return best;
}

function toMapping(demand, choice, reasons = []) {
  const { source, incoming, outgoing, firstAttackQ, lastReleaseQ } = demand;
  return {
    source, target: choice?.target ?? null, player: choice?.player ?? null,
    status: choice ? 'assigned' : 'unfilled', evaluation: choice?.evaluation ?? null,
    carriesIn: incoming.length > 0, carriesOut: outgoing.length > 0, firstAttackQ, lastReleaseQ, reasons,
  };
}

function totalsFor(mappings, ties, switches, priorityConflict) {
  const result = {
    required: 0, optional: 0, requiredMatched: 0, optionalMatched: 0, unfilledRequired: 0, unfilledOptional: 0,
    tieGaps: ties.length, switches: switches.length, priorityConflicts: Number(Boolean(priorityConflict)),
  };
  for (const { source, status } of mappings) {
    if (source.priority === 'required') {
      result.required++;
      if (status === 'assigned') result.requiredMatched++;
      else result.unfilledRequired++;
    } else {
      result.optional++;
      if (status === 'assigned') result.optionalMatched++;
      else result.unfilledOptional++;
    }
  }
  return result;
}

function reviewPriorityConflict(model, demands, choices, optionalCarryPlayers, lastPlayed, switchBeats, requiredMatched) {
  if (!optionalCarryPlayers.length) return null;
  const required = demands.flatMap((demand, index) => demand.source.priority === 'required' ? [index] : []);
  if (required.length === requiredMatched) return null;
  // Check whether holding the optional notes can reduce the coverage of new
  // required roles, including cases where several seats could be reassigned.
  const matrix = required.map((index) => [
    ...choices[index].map((choice) => choice ? 0 : null),
    ...optionalCarryPlayers.map((player) =>
      playerCandidate(model, player, demands[index], lastPlayed.get(player.id), switchBeats, new Set()) ? 0 : null),
  ]);
  const hypothetical = solveAssignment(matrix, required.map(() => 'required'));
  const requiredRecoverable = hypothetical.requiredMatched - requiredMatched;
  return requiredRecoverable > 0 ? { requiredRecoverable, optionalCarryCount: optionalCarryPlayers.length } : null;
}

function planSection(model, section, demands, players, beforePart, lastPlayed, switchBeats) {
  const locked = new Map();
  const occupied = new Set();
  const optionalCarryPlayers = [];
  const unresolved = [];
  const ties = [];
  for (const demand of demands) {
    const before = beforePart.get(demand.source.id);
    if (!demand.incoming.length && !before?.outgoing.length) {
      unresolved.push(demand);
      continue;
    }
    const agrees = tieAgrees(before, demand);
    const old = before?.mapping;
    const reasons = agrees ? ['tie-uncovered'] : ['tie-notation'];
    let choice = null;
    if (agrees && old?.status === 'assigned') {
      if (available(old.player, section)) {
        const evaluation = evaluateMapping(demand.compatibility, old.target, demand.source.role);
        if (evaluation.cost !== null) choice = { player: old.player, target: old.target, evaluation };
        else reasons.push('incompatible');
      } else reasons.push('unavailable');
    }
    if (choice) {
      occupied.add(choice.player.id);
      if (demand.source.priority === 'optional') optionalCarryPlayers.push(choice.player);
    }
    locked.set(demand.source.id, toMapping(demand, choice, choice ? [] : reasons));
    if (!choice) ties.push({ source: demand.source, reason: reasons[0], before: old ?? null });
  }
  const presentParts = new Set(demands.map(({ source }) => source.id));
  for (const { source, outgoing, mapping } of beforePart.values()) {
    if (outgoing.length && !presentParts.has(source.id)) ties.push({ source, reason: 'tie-notation', before: mapping });
  }
  if (section.end === model.measures.length) {
    for (const { source, outgoing } of demands) {
      if (outgoing.length) ties.push({ source, reason: 'tie-notation', before: null });
    }
  }
  const freePlayers = players.filter(({ id }) => !occupied.has(id));
  const rejected = unresolved.map(() => new Set());
  const choices = unresolved.map((demand, index) => freePlayers.map((player) =>
    playerCandidate(model, player, demand, lastPlayed.get(player.id), switchBeats, rejected[index])));
  // Compatibility is recorded in tenths. Scale it so the sum of continuity
  // costs can only break a tie in the total compatibility cost.
  const costScale = 2 * unresolved.length + 1;
  const matrix = choices.map((row) => row.map((choice) => choice
    ? Math.round(choice.evaluation.cost * 10) * costScale + choice.continuityCost : null));
  const solved = solveAssignment(matrix, unresolved.map(({ source }) => source.priority));
  const priorityConflict = reviewPriorityConflict(model, unresolved, choices, optionalCarryPlayers, lastPlayed, switchBeats, solved.requiredMatched);
  const switches = [];
  unresolved.forEach((demand, index) => {
    const choice = choices[index][solved.assigned[index]];
    if (choice?.sw) switches.push(choice.sw);
    let reasons = [];
    if (!choice) {
      if (!players.length) reasons = ['no-player'];
      else if (choices[index].some(Boolean) || !freePlayers.length) reasons = ['player-conflict'];
      else reasons = [...rejected[index]];
    }
    locked.set(demand.source.id, toMapping(demand, choice, reasons));
  });
  const mappings = demands.map(({ source }) => locked.get(source.id));
  mappings.forEach((mapping, index) => {
    if (mapping.status === 'assigned') {
      lastPlayed.set(mapping.player.id, { ...mapping, uncertainRelease: demands[index].uncertainRelease });
    }
  });
  const gaps = { required: [], optional: [], ties };
  for (const mapping of mappings) if (mapping.status === 'unfilled') gaps[mapping.source.priority].push(mapping);
  const totals = totalsFor(mappings, ties, switches, priorityConflict);
  return { ...section, mappings, switches, gaps, totals, priorityConflict };
}

/** Assign a roster to consecutive score ranges [start, end) in written order. */
export function planSections(model, players, { sections, switchBeats = 4 } = {}) {
  if (!model.measures?.length) throw new Error('没有可用于分段的总谱小节。');
  if (!Number.isFinite(switchBeats) || switchBeats < 0) throw new Error('换乐器休止应填写非负的四分音符拍数。');
  validateRoster(players, model.measures.length);
  const ranges = sectionRanges(model.measures, sections);
  const lastPlayed = new Map();
  let beforePart = new Map();
  const planned = [];
  for (const range of ranges) {
    const section = { ...range, startQ: model.measures[range.start].startQ, endQ: model.measures[range.end - 1].endQ };
    const demands = model.parts.flatMap((part) => {
      const demand = demandFor(part, section, beforePart.get(part.id)?.ongoingOut ?? []);
      return demand ? [{ ...demand, section }] : [];
    });
    const result = planSection(model, section, demands, players, beforePart, lastPlayed, switchBeats);
    planned.push(result);
    beforePart = new Map(demands.map((demand, index) => [demand.source.id, { ...demand, mapping: result.mappings[index] }]));
  }
  const totals = totalsFor([], [], [], null);
  for (const result of planned) {
    for (const key of Object.keys(totals)) totals[key] += result.totals[key];
  }
  return { sections: planned, totals, limitations: [...limitations] };
}
