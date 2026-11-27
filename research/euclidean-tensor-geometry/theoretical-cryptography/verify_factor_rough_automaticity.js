"use strict";

// Exact finite checks, no inputs. Only toy primes and known generated products.
let checks = 0;
function verify(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
function gcdBig(a, b) {
  while (b) [a, b] = [b, a % b];
  return a < 0n ? -a : a;
}
function f(n, d = 1n) {
  if (d === 0n) throw Error("zero denominator");
  const g = gcdBig(n, d) * (d < 0n ? -1n : 1n);
  return [n / g, d / g];
}
const plus = ([a, b], [c, d]) => f(a * d + b * c, b * d);
const mul = ([a, b], [c, d]) => f(a * c, b * d);
const div = ([a, b], [c, d]) => f(a * d, b * c);
const eq = (a, b) => a[0] === b[0] && a[1] === b[1];
const gcd = (a, b) => Number(gcdBig(BigInt(a), BigInt(b)));
const lcm = (a, b) => a * b / gcd(a, b);

function squarefreeProducts(P) {
  let items = [{d: 1, omega: 0, primeList: []}];
  for (const p of P) {
    items = items.concat(items.map(item => ({
      d: item.d * p, omega: item.omega + 1, primeList: [...item.primeList, p]
    })));
  }
  return items;
}
for (const K of [1, 2, 3]) {
  for (const P of [[3, 5, 7, 11, 13], [11, 13, 17], [7, 19, 23, 29]]) {
    const pool = squarefreeProducts(P.filter(p => p > 2 * K));
    const G = new Map(), H = new Map(), sign = new Map();
    for (const {d, omega, primeList} of pool) {
      G.set(d, primeList.reduce((u, p) => mul(u, f(BigInt(K), BigInt(p))), f(1n)));
      H.set(d, primeList.reduce((u, p) => mul(u, f(BigInt(K), BigInt(p - K))), f(1n)));
      sign.set(d, omega & 1 ? -1n : 1n);
    }
    const fullMass = pool.reduce((sum, {d}) => plus(sum, H.get(d)), f(0n));
    const reciprocalSieveProduct = P.filter(p => p > 2 * K)
                .reduce((a, p) => mul(a, f(BigInt(p), BigInt(p - K))), f(1n));
    verify(eq(fullMass, reciprocalSieveProduct), "Bernoulli product normalization");
    for (const Z of [1, 7, 11, 30, 70, 105, 400]) {
      const D = pool.map(x => x.d).filter(d => d <= Z);
      const mass = D.reduce((s, d) => plus(s, H.get(d)), f(0n));
      const weights = new Map();
      for (const d of D) {
        let u = f(0n);
        for (const r of D) if (r % d === 0) {
          u = plus(u, mul(f(sign.get(r / d) * sign.get(r)), H.get(r)));
        }
        weights.set(d, div(u, mul(G.get(d), mass)));
        const [wn, wd] = weights.get(d);
        const abs = wn < 0n ? -wn : wn;
        verify(abs <= BigInt(d) * wd, "uniform Selberg weight bound");
      }
      verify(eq(weights.get(1), f(1n)), "normalized empty product");
      let main = f(0n);
      for (const a of D) for (const b of D) {
        main = plus(main, mul(mul(weights.get(a), weights.get(b)), G.get(lcm(a, b))));
      }
      verify(eq(main, div(f(1n), mass)), "Selberg quadratic minimum");
    }
  }
}

for (const [a, c, P] of [[8,[1,3,5],[7,11,13]], [1,[1,4,7,8],[11,13,17]]]) {
  const prod = P.reduce((x, p) => x * p, 1);
  const frequencies = new Map(), k = c.length;
  for (let t = 0; t < prod; t++) {
    const sets = c.map(ci => P.filter(p => (a * t + ci) % p === 0));
    const S = P.filter(p => sets.some(s => s.includes(p)));
    if (sets.every(s => s.length <= 1)) verify(S.length <= k, "exception cardinality");
    const key = S.join(",");
    frequencies.set(key, (frequencies.get(key) || 0) + 1);
  }
  for (const {primeList: S} of squarefreeProducts(P)) {
    const want = P.reduce((n, p) => n * (S.includes(p) ? k : p - k), 1);
    verify(frequencies.get(S.join(",")) === want, "exact CRT exception grouping");
  }
}

const limit = 1024;
const toyPrime = new Uint8Array(limit); toyPrime.fill(1, 2);
for (let p = 2; p * p < limit; p++) if (toyPrime[p]) {
  for (let q = p * p; q < limit; q += p) toyPrime[q] = 0;
}
const toySemi = new Uint8Array(limit), toyBalanced = new Uint8Array(limit);
for (let p = 2; p * p < limit; p++) if (toyPrime[p]) {
  for (let q = p; p * q < limit; q++) if (toyPrime[q]) {
    toySemi[p * q] = 1;
    if (p < q && q <= 2 * p) toyBalanced[p * q] = 1;
  }
}
for (const predicate of [toyPrime, toySemi, toyBalanced]) {
  for (const highFirst of [true, false]) for (const W of [4, 8, 16, 32, 64]) {
    const R = limit / W, patterns = new Map(), half = highFirst ? 0 : W / 2;
    let nRows = 0;
    for (let p = highFirst ? R / 2 : 0; p < R; p++) {
      let row = "";
      for (let t = half; t < W; t++) {
        const n = highFirst ? p * W + t : t * R + p;
        verify(limit / 2 <= n && n < limit, "canonical word");
        row += predicate[n];
      }
      patterns.set(row, (patterns.get(row) || 0) + 1);
      nRows++;
    }
    for (const threshold of [2, 3, 5, 7]) {
      let acceptMass = 0, heavyMass = 0, lightTypes = 0, heavyMax = 0;
      for (const [row, mult] of patterns) {
        const support = [...row].filter(x => x === "1").length;
        acceptMass += mult * support;
        if (mult >= threshold) {
          heavyMass += mult * support;
          heavyMax = Math.max(heavyMax, support);
        } else lightTypes++;
      }
      verify(acceptMass === predicate.slice(limit / 2).reduce((a, b) => a + b, 0),
             "canonical range acceptance mass");
      verify(heavyMass <= nRows * heavyMax, "heavy pattern mass");
      verify(acceptMass - heavyMass <= lightTypes * threshold * W, "light pattern counting");
    }
  }
}
console.log("Passed " + checks + " exact toy identities and inequalities.");
