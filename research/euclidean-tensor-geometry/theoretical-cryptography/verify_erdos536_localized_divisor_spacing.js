'use strict';

// Finite integer checks for FactorErdos536LocalizedDivisorSpacing.md.
// Run with Node.js. The analytic counting inputs are not tested here.
let tests = 0;
function check(ok, label) {
  if (!ok) throw new Error(label);
  ++tests;
}
function gcd(a, b) {
  while (b) [a,b] = [b,a%b];
  return a;
}
function lcm(a, b) { return (a/gcd(a,b))*b; }
function divisors(n) {
  const low = [], high = [];
  for (let d = 1; d*d <= n; ++d) if (n%d === 0) {
    low.push(d);
    if (d*d !== n) high.push(n/d);
  }
  return low.concat(high.reverse());
}
function spaced(ds) {
  return ds.every((d,i) => i === 0 || d >= 2*ds[i-1]);
}
function isPrime(p) {
  if (p < 2) return false;
  for (let d = 2; d*d <= p; ++d) if (p%d === 0) return false;
  return true;
}
const N0 = 190;
const inE = Array.from({length:N0+1}, (_,n) => n >= 1 && spaced(divisors(n)));
let triangleCount = 0;
for (let a = 1; a <= N0; ++a) {
  for (let b = a+1; b <= N0; ++b) {
    const M = lcm(a,b);
    for (let c = b+1; c <= N0; ++c) {
      if (lcm(a,c) !== M || lcm(b,c) !== M) continue;
      ++triangleCount;
      const [x,y,z] = [M/a,M/b,M/c];
      check(gcd(x,y) === 1 && gcd(x,z) === 1 && gcd(y,z) === 1,
        'complements of pairwise equal LCMs are pairwise coprime');
      check(a%y === 0 && a%z === 0 && b%x === 0 &&
        b%z === 0 && c%x === 0 && c%y === 0, 'two complementary divisors in every member');
      check(y*b === z*c && x*a === z*c && z < y && y < x,
        'quotient reversal and exact ratio identity');
      if (c < 2*a) {
        check(y < 2*z && x < 2*z && x < 2*y &&
          !inE[a] && !inE[b] && !inE[c], 'a single factor-two interval excludes the whole triple from E');
      }
    }
  }
}
check(triangleCount > 0, 'nonvacuous triangle census');

const primes = Array.from({length:760}, (_,p) => p).filter(isPrime);
const preimages = new Map();
for (let m = 1; m <= N0; ++m) {
  const ds = divisors(m);
  for (const p of primes) if (p > 2*m) {
    const n = m*p;
    const expect = ds.concat(ds.map(d => d*p));
    const actual = divisors(n);
    check(actual.length === expect.length && actual.every((d,i) => d === expect[i]),
      'exact two-copy divisor structure under prime multiplication');
    check(actual[ds.length] > 2*actual[ds.length-1] && spaced(actual) === inE[m],
      'large prime preserves spacing with a strict cross-copy gap');
    check(!preimages.has(n), 'large-prime preimage is unique');
    preimages.set(n,[m,p]);
  }
}
for (const N of [737, 1061, 2068, 3490, 10000, 32000]) {
  for (const H of [17, 33, Math.floor(N/4),Math.floor(N/2)]) {
    for (const [n,[m,p]] of preimages) {
      if (!inE[m]) continue;
      const lo = Math.floor((N-H)/m)+1, hi = Math.floor(N/m);
      check((N-H < n && n <= N) === (lo <= p && p <= hi), 'exact interval transport for mp');
      if (!(N-H < n && n <= N)) continue;
      check(p > 2*m && spaced(divisors(n)),
        'localized preimage produces a spacing witness');
    }
  }
}
console.log('Localized equal-LCM avoidance: ' + tests.toLocaleString('en-US') + ' exact assertions passed.');
