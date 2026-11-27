/**
 * Match parts to distinct target slots. An unmatched required part has
 * precedence over any number of unmatched optional parts, and an unmatched
 * optional part has precedence over any sum of matched costs.
 *
 * A null matrix entry is an unavailable assignment. Ties are resolved
 * deterministically by input order.
 */
export function solveAssignment(matrix, priorities) {
  if (!Array.isArray(matrix) || !Array.isArray(priorities) || matrix.length !== priorities.length) {
    throw new TypeError('Assignment matrix and priorities must contain the same number of rows.');
  }
  const rows = matrix.length;
  const columns = matrix[0]?.length ?? 0;
  let maximum = 0;
  let allIntegers = true;
  for (let row = 0; row < rows; row++) {
    if (!Array.isArray(matrix[row]) || matrix[row].length !== columns) {
      throw new TypeError('Assignment matrix must be rectangular.');
    }
    if (priorities[row] !== 'required' && priorities[row] !== 'optional') {
      throw new TypeError('Part priorities must be required or optional.');
    }
    for (let column = 0; column < columns; column++) {
      const cost = matrix[row][column];
      if (cost === null) continue;
      if (!Number.isFinite(cost) || cost < 0) {
        throw new TypeError('Assignment edges must be finite nonnegative numbers or null.');
      }
      maximum = Math.max(maximum, cost);
      allIntegers &&= Number.isSafeInteger(cost);
    }
  }

  // Exact integer lifting avoids rounding away a small cost difference
  // after adding the unmatched penalties. Real-valued inputs are binary64,
  // so all are integer multiples of 2^-1074.
  const toUnits = allIntegers ? BigInt : binary64Units();
  const totalCostBound = BigInt(rows) * toUnits(maximum);
  const optionalPenalty = totalCostBound + 1n;
  const requiredPenalty = (BigInt(rows) + 1n) * optionalPenalty;
  const weights = matrix.map((costs, row) => [
    ...costs.map((cost) => cost === null ? null : toUnits(cost)),
    ...matrix.map((_, dummy) => {
      if (dummy !== row) return null;
      return priorities[row] === 'required' ? requiredPenalty : optionalPenalty;
    }),
  ]);
  const result = minimumCostColumns(weights, columns + rows);
  const assigned = result.map((column) => column < columns ? column : null);
  let cost = 0;
  let requiredMatched = 0;
  let optionalMatched = 0;
  assigned.forEach((column, row) => {
    if (column === null) return;
    cost += matrix[row][column];
    if (priorities[row] === 'required') requiredMatched++;
    else optionalMatched++;
  });
  return { assigned, cost, requiredMatched, optionalMatched };
}

function binary64Units() {
  const view = new DataView(new ArrayBuffer(8));
  const implicitBit = 1n << 52n;
  return (value) => {
    view.setFloat64(0, value);
    const bits = view.getBigUint64(0);
    const fraction = bits & (implicitBit - 1n);
    const exponent = (bits >> 52n) & 2047n;
    if (exponent === 0n) return fraction;
    return (implicitBit + fraction) << (exponent - 1n);
  };
}

/** Rectangular Hungarian algorithm, with one guaranteed dummy edge per row. */
function minimumCostColumns(weights, columns) {
  const rows = weights.length;
  const rowPrice = Array(rows + 1).fill(0n);
  const columnPrice = Array(columns + 1).fill(0n);
  const owner = Array(columns + 1).fill(0);
  const origin = Array(columns + 1).fill(0);

  for (let row = 1; row <= rows; row++) {
    owner[0] = row;
    let active = 0;
    const cheapest = Array(columns + 1).fill(null);
    const visited = Array(columns + 1).fill(false);

    do {
      visited[active] = true;
      const part = owner[active];
      let next = 0;
      let delta = null;

      for (let candidate = 1; candidate <= columns; candidate++) {
        if (visited[candidate]) continue;
        const weight = weights[part - 1][candidate - 1];
        if (weight !== null) {
          const reduced = weight - rowPrice[part] - columnPrice[candidate];
          if (cheapest[candidate] === null || reduced < cheapest[candidate]) {
            cheapest[candidate] = reduced;
            origin[candidate] = active;
          }
        }
        if (cheapest[candidate] !== null && (delta === null || cheapest[candidate] < delta)) {
          delta = cheapest[candidate];
          next = candidate;
        }
      }

      for (let column = 0; column <= columns; column++) {
        if (visited[column]) {
          rowPrice[owner[column]] += delta;
          columnPrice[column] -= delta;
        } else if (cheapest[column] !== null) {
          cheapest[column] -= delta;
        }
      }
      active = next;
    } while (owner[active] !== 0);

    do {
      const previous = origin[active];
      owner[active] = owner[previous];
      active = previous;
    } while (active !== 0);
  }

  const result = Array(rows).fill(-1);
  for (let column = 1; column <= columns; column++) {
    if (owner[column] !== 0) result[owner[column] - 1] = column - 1;
  }
  return result;
}
