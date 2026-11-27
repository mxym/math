"use strict";

// Fixed finite checks, only for toy triples with already-known prime factors.
// The oracle uses Legendre factorial valuations, not the digit proof.
const assert = (test, msg) => { if (!test) throw new Error(msg); };
const upper = 2300;
const prime = Array(upper + 1).fill(true);
prime[0] = prime[1] = false;
for (let j = 2; j*j <= upper; ++j) if (prime[j]) {
  for (let t = j*j; t <= upper; t += j) prime[t] = false;
}
const primes = prime.flatMap((isPrime, j) => isPrime ? [j] : []);

function valFactorial(n, l) {
  let s = 0;
  while (n) { n = Math.floor(n/l); s += n; }
  return s;
}
function admissiblePair(n, s, t, remaining) {
  const topS = valFactorial(n, s), topT = valFactorial(n, t);
  let passes = 0;
  for (let j = 1; 2*j <= remaining; ++j) {
    const k = s*t*j;
    const valS = topS - valFactorial(k, s) - valFactorial(n-k, s);
    const valT = topT - valFactorial(k, t) - valFactorial(n-k, t);
    assert(valS >= 0 && valT >= 0, "negative valuation");
    if (valS === 0 && valT === 0) ++passes;
  }
  return passes;
}
const tally = {least: 0, median: 0, twoPrimes: 0, incLeast: 0, gapTie: 0,
               bothPairs: 0, smallD: 0, trialWitnesses: 0};
const first = {};
for (let i = 0; i < primes.length; ++i) {
  const p = primes[i];
  if (p > 2100) break;
  for (let j = i+1; j < primes.length; ++j) {
    const q = primes[j], a = q-p;
    if ((a+2)**2 >= p) break;
    for (let h = j+1; h < primes.length; ++h) {
      const r = primes[h], b = r-p, d = r-q;
      if (b*b >= p) break;
      const n = p*q*r;
      assert(Number.isSafeInteger(n), "inexact fixture");
      const pq = admissiblePair(n, p, q, r);
      const pr = admissiblePair(n, p, r, q);
      const qr = admissiblePair(n, q, r, p);
      tally.trialWitnesses += Math.floor(p/2)+Math.floor(q/2)+Math.floor(r/2);
      const byValuations = qr ? p : pr ? q : pq ? r : p*q;
      const predicted = (d <= a || r <= d*(2*d-1)) ? p :
        (Math.ceil(p/b)+1 <= a+b) ? q : p*q;
      assert(byValuations === predicted, [p,q,r,pq,pr,qr,predicted].join());
      const valR = valFactorial(n,r)-valFactorial(r,r)-valFactorial(n-r,r);
      assert(valR === 0, "r does not escape for k=r");
      if (d > a) {
        assert(!pq, "unexpected first pair");
        assert(!!qr === (r <= d*(2*d-1)), "third-pair boundary");
        assert(pr === Number(Math.ceil(p/b)+1 <= a+b), "middle-pair boundary");
        if (qr) ++tally.incLeast;
        if (qr && pr) ++tally.bothPairs;
      }
      if (d === a) ++tally.gapTie;
      if (d <= a && d === 2) ++tally.smallD;
      const kind = predicted === p ? "least" : predicted === q ? "median" : "twoPrimes";
      ++tally[kind];
      if (!first[kind]) first[kind] = {p,q,r,expected:predicted};
      if (d > a && qr && !first.incLeast) first.incLeast = {p,q,r,expected:p};
    }
  }
}
assert(tally.least && tally.median && tally.twoPrimes && tally.incLeast &&
       tally.gapTie && tally.smallD, "missing phase or edge case");
console.log(JSON.stringify({tally, first}));
