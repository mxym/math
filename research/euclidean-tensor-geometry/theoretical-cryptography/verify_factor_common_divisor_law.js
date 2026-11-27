"use strict";

// Exact arithmetic checks on predetermined small prime samples only.
// Run: node verify_factor_common_divisor_law.js
let checks = 0;
function equal(a, b, label) {
  checks++;
  if (a !== b) throw Error(label + ": " + a + " != " + b);
}
function atMost(a, b, label) {
  checks++;
  if (a > b) throw Error(label + ": " + a + " > " + b);
}
function gcd(a, b) {
  while (b !== 0) [a, b] = [b, a % b];
  return a;
}

const bound = 240;
const isPrime = Array(bound + 1).fill(true);
isPrime[0] = isPrime[1] = false;
for (let p = 2; p * p <= bound; p++) {
  if (isPrime[p]) for (let q = p * p; q <= bound; q += p) isPrime[q] = false;
}
const primes = isPrime.flatMap((yes, n) => yes ? [n] : []);
const mu = Array(bound + 1).fill(1), tau = Array(bound + 1).fill(0);
for (const p of primes) {
  for (let t = p; t <= bound; t += p) mu[t] *= -1;
  for (let t = p * p; t <= bound; t += p * p) mu[t] = 0;
}
for (let d = 1; d <= bound; d++) {
  for (let t = d; t <= bound; t += d) tau[t]++;
}
for (let x = 4; x <= bound / 2; x++) {
  const sample = primes.filter(p => x < p && p <= 2 * x);
  const m = sample.length, hi = 2 * x;
  if (m < 2) continue;
  const off = Array(hi + 1).fill(0), all = Array(hi + 1).fill(0);
  for (const p of sample) for (const q of sample) {
    const d = gcd(p - 1, q - 1);
    all[d]++;
    if (p !== q) off[d]++;
  }
  equal(all.reduce((a, b) => a + b), m * m, "all pair count");
  equal(off.reduce((a, b) => a + b), m * (m - 1), "distinct pair count");
  const divOff = Array(hi + 1).fill(0), divAll = Array(hi + 1).fill(0);
  for (let t = 1; t <= hi; t++) {
    const n = sample.filter(p => (p - 1) % t === 0).length;
    divOff[t] = n * (n - 1);
    divAll[t] = n * n;
    let wantOff = 0, wantAll = 0;
    for (let d = t; d <= hi; d += t) {
      wantOff += off[d];
      wantAll += all[d];
    }
    equal(divOff[t], wantOff, "distinct divisibility count");
    equal(divAll[t], wantAll, "iid divisibility count");
    equal(m * divOff[t] - (m - 1) * divAll[t], -n * (m - n),
          "negative diagonal correction");
    if (t > x) equal(divOff[t], 0, "a common divisor divides the difference");
  }
  let left = 0, right = 0;
  for (let d = hi; d >= 1; d--) {
    let inv = 0;
    for (let k = 1; d * k <= hi; k++) inv += mu[k] * divOff[d * k];
    equal(inv, off[d], "Mobius inversion");
    left += Math.abs(m * off[d] - (m - 1) * all[d]);
    right += tau[d] * Math.abs(m * divOff[d] - (m - 1) * divAll[d]);
    atMost(left, right, "weighted inverted tail comparison");
  }
  atMost(left, 2 * m * (m - 1), "coupled L1 bound for iid and distinct");
}

for (const ell of primes) {
  const p = BigInt(ell);
  const a = p * (p - 2n), b = (p - 1n) ** 2n;
  const betaN = 2n * p - 1n, betaD = a;
  const meanN = p * (p - 1n) + 1n, meanD = p * (p - 1n);
  if (p > 2n) {
    equal(a * (p * betaD + betaN) * meanD, meanN * b * p * betaD,
          "local model mean");
  } else {
    equal(3n * meanD, 2n * meanN, "local mean at two");
  }
  equal((p ** 6n - 1n) * meanD,
        (p ** 2n - 1n) * (p ** 3n - 1n) * p * meanN,
        "zeta quotient local factor");
  const h = 9n, denominator = (p ** (h - 1n) * (p - 1n)) ** 2n;
  // The last bin represents all valuations at least h.
  const tails = [denominator];
  for (let j = 1n; j <= h; j++) tails.push(p ** (2n * (h - j)));
  const mass = tails.map((v, j) => v - (tails[j + 1] || 0n));
  equal(mass.reduce((a, b) => a + b), denominator, "capped normalization");
  equal(mass[0], a * p ** (2n * (h - 1n)), "mass at zero");
  for (let j = 1; j < Number(h); j++) {
    const k = BigInt(j);
    equal(mass[j] * (p - 1n) * p ** (2n * k), denominator * (p + 1n),
          "positive valuation mass");
    equal(mass.slice(j).reduce((a, b) => a + b), tails[j], "local survivor");
  }
}
console.log("Passed " + checks + " exact toy identities and inequalities.");
