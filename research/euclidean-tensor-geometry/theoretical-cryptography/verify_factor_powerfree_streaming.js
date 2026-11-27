"use strict";

// All domains are fixed and small. No arbitrary integer is an input.
let checks = 0;
function requireTrue(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
function gcd(a, b) {
  while (b !== 0) [a, b] = [b, a % b];
  return a;
}
const bound = 1024, isPrime = Array(bound + 1).fill(true);
isPrime[0] = isPrime[1] = false;
for (let p = 2; p * p <= bound; p++) if (isPrime[p]) {
  for (let q = p * p; q <= bound; q += p) isPrime[q] = false;
}
const primes = isPrime.flatMap((yes, n) => yes ? [n] : []);
for (const [b, B, L, k, auxiliary, z] of [
  [2, 20, 16, 2, [3, 5], 359],
  [2, 17, 13, 3, [3], 23]
]) {
  const Y = b ** B, W = b ** L, R = Y / W;
  const small = new Uint8Array(Y), large = new Uint8Array(Y);
  let unionBound = 0;
  for (const p of primes) {
    const power = p ** k;
    if (power >= Y) break;
    const mark = p <= z ? small : large;
    if (p > z) unionBound += Math.floor((Y - 1) / power);
    for (let n = power; n < Y; n += power) mark[n] = 1;
  }
  const product = auxiliary.reduce((a, p) => a * p ** k, 1);
  requireTrue(product > R && auxiliary.every(p => gcd(b, p) === 1),
              "CRT injectivity within the prefix range");
  // A sharper exact lower bound for the number per residue in these small rows.
  const K0 = Math.min(...auxiliary.map(p => Math.min(
    Math.floor(W / (b * p ** k)), Math.floor((W - W / b) / (p ** k)))));
  requireTrue(primes.filter(p => p <= z).length <= K0 / 16, "small prime count");

  for (const highFirst of [true, false]) {
    let mass = 0, goodRows = 0;
    const eligible = [], id = new Set();
    for (let a = 0; a < R; a++) {
      if (highFirst ? a >= R / b : gcd(a, b) === 1) eligible.push(a);
    }
    const lo = highFirst ? 0 : W / b;
    for (const prefix of eligible) {
      const value = t => highFirst ? prefix * W + t : R * t + prefix;
      let big = 0;
      for (let t = lo; t < W; t++) {
        const n = value(t);
        requireTrue(Y / b <= n && n < Y, "legal canonical continuation");
        big += large[n];
      }
      mass += big;
      if (big > K0 / 16) continue;
      goodRows++;
      const residues = [];
      for (const ell of auxiliary) {
        const P = ell ** k;
        const K = Array(P).fill(0), smallBad = Array(P).fill(0), accepts = Array(P).fill(0);
        let distinguished = -1;
        for (let t = lo; t < W; t++) {
          if (highFirst && t % b !== 1) continue;
          const n = value(t), cell = t % P;
          K[cell]++;
          if (!(n % P)) {
            requireTrue(distinguished < 0 || distinguished === cell, "single forbidden residue");
            distinguished = cell;
          }
          smallBad[cell] += small[n];
          accepts[cell] += !small[n] && !large[n];
        }
        requireTrue(distinguished >= 0 && accepts[distinguished] === 0, "forbidden residue rejected");
        for (let i = 0; i < P; i++) if (i !== distinguished) {
          requireTrue(K[i] >= K0, "uniform candidate floor");
          requireTrue(smallBad[i] * 16 <= K[i] * 13, "small-square union budget");
          requireTrue(accepts[i] > 0, "a free representative in every other residue");
        }
        residues.push(distinguished);
      }
      const key = residues.join(",");
      requireTrue(!id.has(key), "root pattern distinguishes the prefix");
      id.add(key);
    }
    requireTrue(goodRows >= eligible.length / 2, "nonvacuous good-row fraction");
    requireTrue(mass <= unionBound, "global union count over disjoint rows");
  }
}

for (const k of [2, 3, 4]) {
  const selected = [3, 5, 7];
  for (const p of selected) for (let x = 0; x <= 1; x++) for (let y = 0; y <= 1; y++) {
    requireTrue(((1 - x + 1 - y) % (p ** k) === 0) === (x && y ? true : false),
                "disjointness encoding truth table");
  }
}
// A small concrete padding progression verifies the CRT choices and its count error.
for (let x = 0; x <= 1; x++) for (let y = 0; y <= 1; y++) {
  const h = 6, J = 9, k = 2;
  const high = Array.from({length: 2 ** (h - 1)}, (_, a) => a + 2 ** (h - 1))
                    .find(a => (a * 2 ** J) % 9 === 1 - x);
  const low = Array.from({length: 2 ** J}, (_, L) => L)
                   .filter(L => L % 9 === 1 - y && L % 4 === 1);
  requireTrue(high !== undefined && low.length > 0, "nonempty private CRT classes");
  for (const L of low) {
    const N = high * 2 ** J + L;
    requireTrue(2 ** (h + J - 1) <= N && N < 2 ** (h + J), "canonical input length");
    requireTrue(N % 4 === 1 && ((N % 9 === 0) === (x === 1 && y === 1)), "forced square");
  }
  for (const p of primes.filter(p => 3 < p && p < 181)) {
    const divisible = low.filter(L => (high * 2 ** J + L) % (p ** k) === 0).length;
    requireTrue(Math.abs(divisible * p ** k - low.length) <= p ** k,
                "padding square probability and endpoint error");
  }
}

console.log("Passed " + checks + " exact toy identities and inequalities.");
