"use strict";

// Exact tests of padded integers formed from fixed toy Boolean cores.
// No inputs, no prime generation or factor computation.
let checks = 0;
function check(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
const two = j => 1n << BigInt(j);
const bit = (x, j) => Number((x >> BigInt(j)) & 1n);
function makeCore(m, n, first) {
  let out = BigInt(first ? 4 : 6) * two(m * m);
  for (let j = 0; j < m; j++) {
    if (n & (1 << j)) out += two(first ? j : m * j);
  }
  return out;
}
const seen = new Set();
for (let m = 1; m <= 6; m++) {
  // The toy guard has the same exact relation as the proof.
  const C = m * m + 3, B = 5 * m * m + 24, G = B - C, H = G - C - 3;
  const pad = two(H), mask = two(G) - pad;
  const offsets = [[0n, 0n], [pad - 1n, 0n], [0n, pad - 1n],
                   [pad - 1n, pad - 1n], [pad / 2n, pad / 3n]];
  let diagonal = 0;
  seen.clear();
  for (let x = 0; x < 1 << m; x++) for (let y = 0; y < 1 << m; y++) {
    const a = makeCore(m, x, true), b = makeCore(m, y, false);
    const z = [];
    for (const [r, s] of offsets) {
      const p = a * two(G) + r, q = b * two(G) + s, product = p * q;
      check(two(B-1) <= p && p < q && q < two(B) && q < 2n * p,
            "balanced canonical width");
      check((p & mask) === 0n && (q & mask) === 0n, "guard bits");
      check(product / two(2 * G) === a * b, "no carry into the core product");
      for (let i = 0; i < m; i++) {
        check(bit(p, G + i) === ((x >> i) & 1), "first core variable position");
        check(bit(q, G + m * i) === ((y >> i) & 1), "second core variable position");
        for (let j = 0; j < m; j++) {
          const u = ((x >> i) & 1) * ((y >> j) & 1);
          check(bit(product, 2 * G + i + m * j) === u, "selected product bit");
        }
      }
    }
    let separator = 0;
    for (let i = 0; i < m; i++) {
      const xbit = (x >> i) & 1, ybit = (y >> i) & 1;
      const slack = xbit + ybit - 2 * xbit * ybit;
      check(slack >= 0 && slack === (xbit ^ ybit), "coordinate disagreement slack");
      separator += slack;
      for (let j = 0; j < m; j++) z.push(xbit * ((y >> j) & 1));
    }
    check((separator === 0) === (x === y), "diagonal face equation");
    if (separator === 0) {
      diagonal++;
      const label = z.join("");
      check(!seen.has(label), "distinct correlation vertices on the face");
      seen.add(label);
    }
  }
  check(diagonal === 1 << m && seen.size === diagonal, "all diagonal profiles");
}
console.log("Passed " + checks + " exact toy identities and inequalities.");
