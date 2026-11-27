"use strict";

// Finite identities on small predetermined domains. No input is accepted.
let checks = 0;
function requireTrue(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
const modulo = (x, n) => ((x % n) + n) % n;
function gcd(a, b) {
  while (b !== 0) [a, b] = [b, a % b];
  return a;
}
function lcm(a, b) { return a * b / gcd(a, b); }
const units = n => Array.from({length: n}, (_, j) => j).filter(j => gcd(j, n) === 1);
const char4 = x => !(x % 2) ? 0 : (x % 4 === 1 ? 1 : -1);
const char8 = x => !(x % 2) ? 0 : (x % 8 === 1 || x % 8 === 7 ? 1 : -1);
function legendre(p) {
  const good = new Set(Array.from({length: p - 1}, (_, j) => (j + 1) ** 2 % p));
  return x => !(x % p) ? 0 : (good.has(x % p) ? 1 : -1);
}
const characters = [[3, legendre(3)], [5, legendre(5)], [7, legendre(7)],
                    [11, legendre(11)], [8, char8]];
for (const [d, chi] of characters) {
  const L = lcm(4, d), u = units(L);
  requireTrue(u.reduce((s, v) => s + char4(v) * chi(v), 0) === 0,
              "twisted character has no principal part");
  requireTrue(u.reduce((s, v) => s + char4(v) * chi(v) ** 2, 0) === 0,
              "twisted character has no original-character part");
}
for (let r = 2; r <= 96; r++) {
  const U = units(r);
  for (const [d, chi] of characters) if (r % d === 0) {
    for (const a of U.slice(0, 3)) for (const p of U) {
      // Coefficient vectors use formal r-th root powers, no floating point.
      const left = Array(r).fill(0), right = Array(r).fill(0);
      for (const v of U) {
        left[(a * p * v) % r] += chi(v);
        right[(a * v) % r] += chi(p) * chi(v);
      }
      for (let z = 0; z < r; z++) {
        requireTrue(left[z] === right[z], "twisted unit reindexing");
      }
    }
  }
}
for (let r = 2; r <= 72; r++) for (const a of units(r)) {
  for (const correction of [-1, 0, 1]) for (const anchor of [0, 1, 23, 97]) {
    const buckets = Array(r).fill(0);
    for (let j = 0; j < r; j++) {
      // Angle (ar + correction)/r^2, with distance from a/r <= 1/r^2.
      const fracNumerator = modulo((a * r + correction) * (anchor + j), r * r);
      buckets[Math.floor(fracNumerator / r)]++;
    }
    requireTrue(Math.max(...buckets) <= 4, "rational mesh occupancy");
  }
}
for (let j = 0; j <= 12; j++) {
  const Q = 2 ** (j + 1);
  for (const half of [0, 1]) {
    const lo = half * Q / 2, hi = lo + Q / 2;
    const f = Array.from({length: Q}, (_, t) => +(lo <= t && t < hi));
    requireTrue(f.reduce((a, b) => a + b) === Q / 2, "half interval size");
    for (let k = 0; k < Q; k++) {
      requireTrue(f[k] - f[modulo(k - 1, Q)] === +(k === lo) - +(k === hi % Q),
                  "geometric-series telescoping coefficient");
    }
  }
}

// Test the exact leaf counting/advantage identity, not the asymptotic bound.
const smallPrimes = [53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
const toy = [];
for (let p = 0; p < smallPrimes.length; p++) for (let q = p + 1; q < smallPrimes.length; q++) {
  toy.push([smallPrimes[p] * smallPrimes[q], char4(smallPrimes[p])]);
}
for (let depth = 0; depth <= 7; depth++) for (let seed = 0; seed < 31; seed++) {
  const totals = new Map();
  for (const [N, sign] of toy) {
    let path = "", history = seed;
    for (let step = 0; step < depth; step++) {
      const digit = (history + 5 * step) % 14, answer = (N >>> digit) & 1;
      path += answer;
      history = 3 * history + 5 * answer + 1;
    }
    const cell = totals.get(path) || [0, 0];
    cell[sign > 0 ? 0 : 1]++;
    totals.set(path, cell);
  }
  requireTrue(totals.size <= 2 ** depth, "leaf cap");
  const sum = [...totals.values()].reduce((z, [a, b]) => z + a + b, 0);
  const optimum = [...totals.values()].reduce((z, [a, b]) => z + Math.max(a, b), 0);
  const absoluteSigned = [...totals.values()].reduce((z, [a, b]) => z + Math.abs(a - b), 0);
  requireTrue(sum === toy.length && 2 * optimum - toy.length === absoluteSigned,
              "exact joint variation and best fixed per-leaf decision");
}
console.log("Passed " + checks + " exact toy identities and inequalities.");
