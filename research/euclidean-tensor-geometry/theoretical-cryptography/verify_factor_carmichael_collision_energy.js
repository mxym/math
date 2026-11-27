"use strict";

// Finite exact checks on fixed toy data; no input is accepted.
// Run: node verify_factor_carmichael_collision_energy.js
let checks = 0;
function requireTrue(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
function gcd(a, b) {
  while (b !== 0) [a, b] = [b, a % b];
  return a;
}
const lcm = (a, b) => (a / gcd(a, b)) * b;
const bound = 1024;
const isPrime = Array(bound + 1).fill(true);
isPrime[0] = isPrime[1] = false;
for (let p = 2; p * p <= bound; p++) if (isPrime[p]) {
  for (let q = p * p; q <= bound; q += p) isPrime[q] = false;
}
const primes = isPrime.flatMap((yes, n) => yes ? [n] : []);
const counts = {disjoint: 0, shared: 0, differentGcds: 0, sameGcds: 0};

function grid(a, b, c, d) {
  const A = gcd(a, c), B = gcd(a, d), C = gcd(b, c), D = gcd(b, d);
  requireTrue(A * B === a && C * D === b && A * C === c && B * D === d,
              "four-coordinate product identity");
  return [A, B, C, D];
}

for (let a = 1; a <= 28; a++) for (let b = 1; b <= 28; b++) {
  if (gcd(a, b) !== 1) continue;
  for (let c = 1; c <= 40; c++) if ((a * b) % c === 0) {
    const d = a * b / c;
    if (gcd(c, d) === 1) grid(a, b, c, d);
  }
}

for (let X = 9; X <= bound / 2; X++) {
  const pool = primes.filter(p => X < p && p <= 2 * X);
  const fibers = new Map();
  for (let j = 0; j < pool.length; j++) for (let k = j + 1; k < pool.length; k++) {
    const p = pool[j], q = pool[k], key = lcm(p - 1, q - 1);
    if (!fibers.has(key)) fibers.set(key, []);
    fibers.get(key).push([p, q]);
  }
  let nPairs = 0, conditionalExtras = 0, imageDeficit = 0;
  let repeatedInputs = 0, undirectedCollisions = 0;
  for (const pairs of fibers.values()) {
    const f = pairs.length;
    nPairs += f;
    conditionalExtras += f * (f - 1);
    imageDeficit += f - 1;
    if (f > 1) repeatedInputs += f;
    for (let j = 0; j < f; j++) for (let k = j + 1; k < f; k++) {
      undirectedCollisions++;
      const [p, q] = pairs[j], [r, s] = pairs[k];
      const g = gcd(p - 1, q - 1), h = gcd(r - 1, s - 1);
      const i = gcd(g, h), u = g / i, v = h / i;
      requireTrue(u <= 16 * v && v <= 16 * u, "gcd comparability");
      if (g !== h) counts.differentGcds++; else counts.sameGcds++;
      if (new Set([p, q, r, s]).size === 3) {
        counts.shared++;
        const same = [p, q].find(x => x === r || x === s);
        const left = p === same ? q : p, right = r === same ? s : r;
        requireTrue(u !== v && (left - 1) * h === (right - 1) * g,
                    "distinct shared-prime forms");
        requireTrue((same - 1) % (i * u * v) === 0, "shared-prime modulus");
        continue;
      }
      counts.disjoint++;
      const a = (p - 1) / g, b = (q - 1) / g;
      const c = (r - 1) / h, d = (s - 1) / h;
      const v1 = gcd(a, v), v2 = gcd(b, v), u1 = gcd(c, u), u2 = gcd(d, u);
      requireTrue(v1 * v2 === v && u1 * u2 === u, "coefficient splitting");
      const [A, B, C, D] = grid(a / v1, b / v2, c / u1, d / u2);
      const k1 = g * v1, k2 = g * v2, k3 = h * u1, k4 = h * u2;
      requireTrue(k1 * A * B + 1 === p && k2 * C * D + 1 === q &&
                  k3 * A * C + 1 === r && k4 * B * D + 1 === s, "forms");
      requireTrue(k1 * A !== k4 * D && k3 * A !== k2 * D &&
                  k1 * B !== k3 * C && k4 * B !== k2 * C, "distinct sieve pairs");
      let A0 = 1;
      while (2 * A0 <= A) A0 *= 2;
      // Scales as integer numerator/denominator pairs. Cross-multiply.
      const scales = [[A0, 1], [X, k1 * A0], [X, k3 * A0], [k1 * A0, k4]];
      for (const [j, value] of [A, B, C, D].entries()) {
        const [num, den] = scales[j];
        requireTrue(num <= 8 * den * value && den * value <= 8 * num,
                    "dyadic coordinate scales");
      }
      const [volN, volD] = scales.reduce(([a, b], [n, d]) => [a * n, b * d], [1, 1]);
      requireTrue(volN * h * h * u === X * X * volD, "weighted box volume");
    }
  }
  requireTrue(nPairs === pool.length * (pool.length - 1) / 2, "domain size");
  requireTrue(nPairs - imageDeficit === fibers.size, "image deficit");
  requireTrue(conditionalExtras === 2 * undirectedCollisions, "energy identity");
  requireTrue(repeatedInputs <= conditionalExtras &&
              2 * imageDeficit <= conditionalExtras, "energy controls deficit");
}

for (let a = 1; a <= 24; a++) for (let b = a + 1; b <= 24; b++) {
  for (const ell of primes.filter(p => 2 < p && p < 44)) {
    let roots = 0;
    for (let r = 0; r < ell; r++) roots += ((a * r + 1) * (b * r + 1)) % ell === 0;
    requireTrue(roots <= 2, "at most two local roots");
    if ((a * b * (b - a)) % ell !== 0) requireTrue(roots === 2, "generic two roots");
  }
}
requireTrue(Object.values(counts).every(n => n > 0), "both overlap and gcd regimes exercised");
console.log("Passed " + checks + " exact toy checks; collision bins: " + JSON.stringify(counts));
