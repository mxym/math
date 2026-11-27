"use strict";

// Exact checks on toy prime pools and predetermined masks. No input.
let checks = 0, testedMasks = 0, degreeChecks = 0;
function requireTrue(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
const bound = 1024, isPrime = Array(bound + 1).fill(true);
isPrime[0] = isPrime[1] = false;
for (let p = 2; p * p <= bound; p++) if (isPrime[p]) {
  for (let q = p * p; q <= bound; q += p) isPrime[q] = false;
}
const primes = isPrime.flatMap((yes, n) => yes ? [n] : []);
function positionSums(positions) {
  let sums = [0];
  for (const j of positions) sums = sums.concat(sums.map(s => s + 2 ** j));
  return sums;
}
function positionMask(positions) {
  return positions.reduce((m, j) => m + (1 << j), 0);
}
let randomState = 0x5b47cd31;
function shuffle(a) {
  a = a.slice();
  for (let i = a.length - 1; i > 0; i--) {
    randomState ^= randomState << 13;
    randomState ^= randomState >>> 17;
    randomState ^= randomState << 5;
    const j = (randomState >>> 0) % (i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function exceptionSet(positions, pool, n) {
  const bad = new Set();
  let nonzero = 0;
  function enumerate(i, value, nz) {
    if (i === positions.length) {
      if (!nz) return;
      nonzero++;
      requireTrue(value !== 0 && Math.abs(value) < 2 ** (2 * n), "signed sum bounds");
      const divisors = pool.filter(p => value % p === 0);
      requireTrue(divisors.length <= 2, "at most two n-bit primes per signed sum");
      for (const p of divisors) bad.add(p);
      return;
    }
    const pow = 2 ** positions[i];
    enumerate(i + 1, value - pow, true);
    enumerate(i + 1, value, nz);
    enumerate(i + 1, value + pow, true);
  }
  enumerate(0, 0, false);
  requireTrue(nonzero === 3 ** positions.length - 1, "signed vector count");
  requireTrue(bad.size <= 2 * nonzero, "exception upper bound");
  const sums = positionSums(positions);
  for (const p of pool) {
    const modularInjective = new Set(sums.map(t => t % p)).size === sums.length;
    requireTrue(modularInjective !== bad.has(p), "exception equals modular non-injection");
  }
  testedMasks++;
  return bad;
}

for (let n = 4; n <= 9; n++) {
  const pool = primes.filter(p => 2 ** (n - 1) <= p && p < 2 ** n);
  const all = Array.from({length: 2 * n}, (_, j) => j);
  const layouts = [all, all.slice().reverse(),
                   all.filter(j => !(j % 2)).concat(all.filter(j => j % 2))];
  for (let j = 0; j < 21; j++) layouts.push(shuffle(all));
  for (const order of layouts) {
    const subsize = Math.min(4, Math.floor(3 * n / 5));
    for (let k = Math.ceil(3 * n / 4); k <= Math.floor(5 * n / 4); k++) {
      const A = order.slice(0, k), B = order.slice(k);
      const JA = A.slice(0, subsize), JB = B.slice(0, subsize);
      const bad = new Set([...exceptionSet(JA, pool, n), ...exceptionSet(JB, pool, n)]);
      const masks = [positionMask(A), positionMask(B)];
      const degrees = [new Map(), new Map()], caps = [2 ** (B.length - subsize),
                                                     2 ** (A.length - subsize)];
      let discarded = 0, good = 0;
      for (let i = 0; i < pool.length; i++) for (let j = i + 1; j < pool.length; j++) {
        const p = pool[i], q = pool[j];
        if (bad.has(p) || bad.has(q)) { discarded++; continue; }
        good++;
        const product = p * q;
        for (const label of [p, q]) for (let v = 0; v < 2; v++) {
          const key = (product & masks[v]) + "/" + label;
          const old = (degrees[v].get(key) || 0) + 1;
          degrees[v].set(key, old);
          requireTrue(old <= caps[v], "observed word per-label capacity");
          degreeChecks++;
        }
      }
      requireTrue(discarded <= bad.size * (pool.length - 1), "input exception mass");
      requireTrue(discarded + good === pool.length * (pool.length - 1) / 2, "input partition");
      requireTrue(2 ** A.length * caps[0] === 2 ** (2 * n - subsize) &&
                  2 ** B.length * caps[1] === 2 ** (2 * n - subsize), "cut capacities");
    }
  }
}

function schedules(bits, visits) {
  if (visits === 1) return 1;
  let sum = 0;
  for (let n = 0; n <= bits; n++) sum += schedules(bits - n, visits - 1);
  return sum;
}
function choose(n, k) {
  let binom = 1;
  for (let j = 1; j <= k; j++) binom = binom * (n + 1 - j) / j;
  return binom;
}
for (let n = 0; n <= 12; n++) for (let visits = 1; visits <= 7; visits++) {
  requireTrue(schedules(n, visits) === choose(n + visits - 1, visits - 1),
              "weak composition length count");
}
requireTrue(degreeChecks > 0, "good inputs exercised");
console.log("Passed " + checks + " exact toy checks, including " + testedMasks +
            " mask replays and " + degreeChecks + " local degree increments.");
