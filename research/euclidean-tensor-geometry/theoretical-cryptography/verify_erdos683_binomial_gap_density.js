'use strict';

// Finite exact checks for FactorErdos683BinomialGapDensity.md.
// Run with Node.js. No asymptotics are inferred from these checks.
let tests = 0;
function check(ok, label) { if (!ok) throw new Error(label); ++tests; }
const U = 225;
const largest = Array(U+1).fill(1), primes = [];
for (let p = 2; p <= U; ++p) if (largest[p] === 1) {
  primes.push(p);
  for (let m = p; m <= U; m += p) largest[m] = p;
}
function lastPrime(n) {
  for (let i = primes.length-1; i >= 0; --i) if (primes[i] <= n) return primes[i];
}
function vpFact(n,p) {
  let s = 0;
  while (n > 0) {
    n = Math.floor(n/p);
    s += n;
  }
  return s;
}
for (let n = 4; n <= U; ++n) {
  const p = lastPrime(n), D = n-p, M = [1];
  check(2*p > n && 2*D < n, 'preceding prime yields a legal gap index');
  const bin = [1n];
  for (let k = 1; 2*k <= n; ++k) {
    const r = bin[k-1]*BigInt(n-k+1);
    check(r%BigInt(k) === 0n, 'exact binomial recurrence');
    bin[k] = r/BigInt(k);
    const z = BigInt(k);
    const head = n-k+1;
    M[k] = Math.max(M[k-1],largest[head]);
    const primesInBinom = primes.filter(q => bin[k]%BigInt(q) === 0n);
    const actual = primesInBinom[primesInBinom.length-1];
    check(M[k] === actual && actual > k, 'largest numerator factor survives binomial denominator');
    for (const q of primes) if (q > k && q <= n) {
      const occurs = Math.floor(n/q) > Math.floor((n-k)/q);
      check((bin[k]%BigInt(q) === 0n) === occurs, 'prime above the denominator factor range');
    }
    if (k > D) {
      check(actual === p && p >= head, 'past the gap, the exact largest factor is the preceding prime');
    } else {
      check(largest[head] !== head && 2*M[k] <= n && 2*head > n,
        'inside the gap all numerator terms are composite');
    }
    const detailed = primes.filter(q => vpFact(n,q) > vpFact(k,q)+vpFact(n-k,q));
    check(detailed.length === primesInBinom.length &&
      detailed[detailed.length-1] === actual, 'independent Legendre numerator/denominator check');
    check(z <= BigInt(actual), 'ordinary Sylvester-Schur baseline');
  }
  // Check equation (2a) without logs by using each rational b=s/t.
  for (let t = 1; t <= 4; ++t) {
    for (let s = 0; s <= 20; ++s) {
      const a = BigInt(s), b = BigInt(t);
      let goodAll = true, goodGap = true;
      for (let k = 1; 2*k <= n; ++k) {
        const N = BigInt(n-k+1)**b, K = BigInt(k)**a, m = BigInt(M[k])**b;
        if (m < (N < K ? N : K)) goodAll = false;
        if (2 <= k && k <= D && BigInt(M[k])**b < K) goodGap = false;
      }
      check(goodAll === goodGap, 'whole-row feasibility is equivalent to the gap-prefix checks');
      if (D >= 2 && 2n**b * BigInt(D)**a > BigInt(n)**b) {
        check(!goodAll, 'gap endpoint forces the deterministic upper bound');
      }
    }
  }
}
console.log('Binomial prime-gap reduction: ' + tests.toLocaleString('en-US') + ' exact assertions passed.');
