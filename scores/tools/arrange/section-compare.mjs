import { planSections } from './section-planner.mjs';

const omittedReason = 'optional-layer-omitted';
export const comparisonReasons = {
  'exhausted-candidates': '本次整条可选层取舍范围已比较完',
  'plan-budget': '达到候选数量上限',
  'time-budget': '达到比较时间上限',
  'cancelled': '设置改变，比较已取消',
};

function objective(plan) {
  let cost = 0;
  for (const section of plan.sections) for (const row of section.mappings) {
    if (row.status === 'assigned') cost += row.evaluation?.cost ?? 0;
  }
  // Lower is better; these are diagnostics for the written-order baseline,
  // not a certificate for the unrestricted arrangement problem.
  return [-plan.totals.requiredMatched, plan.totals.tieGaps, -plan.totals.optionalMatched, cost, plan.totals.switches];
}

function better(left, right) {
  for (let index = 0; index < left.length; index++) {
    if (Math.abs(left[index] - right[index]) < 1e-8) continue;
    return left[index] < right[index];
  }
  return false;
}

function* choices(ids) {
  // Try single-layer changes before combinations. The bounded prefix is
  // deterministic and prefers layers already seen holding a cross-section tie.
  for (let size = 1; size <= ids.length; size++) {
    const indices = Array.from({length:size}, (_, index) => index);
    while (true) {
      yield indices.map(index => ids[index]);
      let cursor = size - 1;
      while (cursor >= 0 && indices[cursor] === ids.length - size + cursor) cursor--;
      if (cursor < 0) break;
      indices[cursor]++;
      for (let next = cursor + 1; next < size; next++) indices[next] = indices[next - 1] + 1;
    }
  }
}

function restoreOmittedRows(candidate, baseline, omitted) {
  const totals = Object.fromEntries(Object.keys(baseline.totals).map(key => [key, 0]));
  const sections = candidate.sections.map((section, index) => {
    const original = baseline.sections[index];
    const omittedRows = original.mappings.filter(row => omitted.has(row.source.id)).map(row => ({
      ...row, target:null, player:null, status:'unfilled', evaluation:null,
      reasons:[omittedReason], omitted:true,
    }));
    const byId = new Map([...section.mappings, ...omittedRows].map(row => [row.source.id, row]));
    const mappings = original.mappings.map(row => byId.get(row.source.id)).filter(Boolean);
    const tally = {...section.totals,
      optional:original.totals.optional,
      unfilledOptional:original.totals.optional - section.totals.optionalMatched,
    };
    for (const key of Object.keys(totals)) totals[key] += tally[key];
    return {...section, mappings, totals:tally, gaps:{...section.gaps,optional:[...section.gaps.optional,...omittedRows]}};
  });
  return {...candidate,sections,totals};
}

/**
 * Bounded comparison of whole optional layers, followed by the unchanged
 * written-order solver for each subset. It can repair an optional held layer
 * blocking a later required part, but does not search every seat/instrument
 * trajectory, arbitrary phrase omissions, or the performed repeat path.
 */
export async function compareOptionalLayers(model, players, {
  sections, switchBeats=4, maxPlans=32, maxMillis=1500,
  cancelled=()=>false, yieldControl=async()=>{}, now=()=>performance.now(),
}={}) {
  if (!Number.isSafeInteger(maxPlans) || maxPlans < 1 || maxPlans > 128) throw new Error('比较数量须为 1 至 128 个方案。');
  if (!Number.isFinite(maxMillis) || maxMillis < 0 || maxMillis > 10000) throw new Error('比较时长须为 0 至 10 秒。');
  const started = now();
  const options = {sections,switchBeats};
  const baseline = planSections(model,players,options);
  const optional = new Set(model.parts.filter(part=>part.priority==='optional').map(part=>part.id));
  const active = new Set(baseline.sections.flatMap(section=>section.mappings.filter(row=>optional.has(row.source.id)).map(row=>row.source.id)));
  const carries = new Set(baseline.sections.flatMap(section=>section.mappings.filter(row=>optional.has(row.source.id)&&row.carriesOut).map(row=>row.source.id)));
  const ids = [...carries,...[...active].filter(id=>!carries.has(id))];
  const totalCandidates = 1n << BigInt(ids.length);
  let tested = 1, best = baseline, bestValue = objective(baseline), omittedIds = [], termination = 'exhausted-candidates';
  for (const omitted of choices(ids)) {
    await yieldControl();
    if (cancelled()) {termination='cancelled';break;}
    if (tested >= maxPlans) {termination='plan-budget';break;}
    if (now()-started >= maxMillis) {termination='time-budget';break;}
    const omittedSet = new Set(omitted);
    const reduced = {...model,parts:model.parts.filter(part=>!omittedSet.has(part.id))};
    const candidate = restoreOmittedRows(planSections(reduced,players,options),baseline,omittedSet);
    tested++;
    const value = objective(candidate);
    if (better(value,bestValue)) {best=candidate;bestValue=value;omittedIds=[...omitted];}
  }
  if (cancelled()) termination='cancelled';
  const report = {
    method:'bounded-whole-optional-layer-comparison',
    optimality:'not-certified',
    tested, totalCandidates:totalCandidates.toString(),
    maxPlans,maxMillis,elapsedMillis:Math.max(0,Math.round(now()-started)),termination,
    allLayerSubsetsTested:BigInt(tested)===totalCandidates,
    omittedIds,
    omittedNames:omittedIds.map(id=>model.parts.find(part=>part.id===id)?.name??id),
    objectiveOrder:['必保声部段覆盖（多）','延音待核项（少）','可选声部段覆盖（多）','适配代价（低）','换乐器次数（少）'],
    baselineObjective:objective(baseline),candidateObjective:bestValue,
    improved:better(bestValue,objective(baseline)),
    explanation:'先比较必保声部段覆盖，再比较延音待核项、可选覆盖和适配代价。仅取舍整条可选声部，每个候选仍按书面顺序逐段求解。未证明全曲最优，不拆断已保留的延音链。',
  };
  return {baseline,candidate:best,report};
}
