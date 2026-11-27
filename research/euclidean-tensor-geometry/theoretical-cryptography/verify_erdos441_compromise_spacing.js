'use strict';

// Finite checks for FactorErdos441CompromiseSpacing.md.
// Run: node verify_erdos441_compromise_spacing.js
// All Number arithmetic here is on small exact integers. CRT products
// and powers of larger integers are represented as BigInt.

let assertions = 0;
function check(ok, label) {
  if (!ok) throw new Error(label);
  ++assertions;
}
function gcd(a, b) {
  while (b) [a, b] = [b, a % b];
  return a;
}
function lcm(a, b) { return (a / gcd(a, b)) * b; }
function ceilDiv(a, b) { return Math.floor((a+b-1)/b); }
function factors(n) {
  const f = [];
  for (let p = 2; p*p <= n; ++p) {
    if (n%p === 0) {
      f.push(p);
      while (n%p === 0) n /= p;
    }
  }
  if (n > 1) f.push(n);
  return f;
}
function prime(n) { const f = factors(n); return n >= 2 && f.length === 1 && f[0] === n; }

for (let k = 2; k <= 150; ++k) {
  for (let n = k+1; n <= k+45; ++n) {
    check(n*(k+1) >= (n+1)*k, 'successive rational-grid hulls overlap');
  }
  for (let z = k*(k+1); z <= k*(k+120); ++z) {
    const n = Math.floor(z/k), a = z%k, b = n-a;
    check(a >= 0 && b >= 0 && n >= k+1 &&
      a*(k+1)+b*k === z, 'two nearby reciprocal denominators fill the exact grid');
  }
}
for (let P = 1; P <= 70; ++P) {
  for (let d = 1; d <= 28; ++d) {
    const n0 = ceilDiv(P,d);
    for (let U = n0*P; U <= n0*P+250; ++U) {
      const n = Math.floor(U/P);
      const b = ceilDiv(U-n*P,d);
      const hit = n*P+b*d;
      check(n >= n0 && b >= 0 && b <= n && U <= hit && hit < U+d,
        'overlapping equal-count intervals meet any full mesh window');
    }
  }
}

function lists(lo, hi) {
  return Array.from({length:hi-lo+1}, (_,j) => factors(lo+j));
}
// Independent Boolean witness test for small intervals. A shared prime
// dividing t-s may appear in either family. Otherwise its assignment is
// red or blue, but not both.
function directlyCompatible(first, second, delta) {
  const constraints = [];
  for (const [F, color] of [[first,0], [second,1]]) {
    for (const fs of F) if (!fs.some(p => delta%p === 0)) constraints.push([fs,color]);
  }
  constraints.sort((a,b) => a[0].length-b[0].length);
  const owner = new Map();
  function visit(i) {
    if (i === constraints.length) return true;
    const [fs,color] = constraints[i];
    if (fs.some(p => owner.get(p) === color)) return visit(i+1);
    for (const p of fs) if (!owner.has(p)) {
      owner.set(p,color);
      const yes = visit(i+1);
      owner.delete(p);
      if (yes) return true;
    }
    return false;
  }
  return visit(0);
}
for (const [num,den] of [[1,4],[1,2],[2,3],[4,5]]) {
  for (let s = 2; s <= 42; ++s) {
    const hi = Math.floor((num+den)*s/den);
    const first = lists(s,hi);
    let M = 1n;
    for (let p = 2; p <= hi; ++p) {
      if (prime(p) && (p >= s || p*p <= hi)) M *= BigInt(p);
    }
    for (const fs of first) {
      check(fs.some(p => M%BigInt(p) === 0n), 'CRT modulus supplies a first-window divisor');
    }
    const tBig = BigInt(s)+M;
    for (const fs of first) {
      const use = fs.find(p => M%BigInt(p) === 0n);
      check((tBig-BigInt(s))%BigInt(use) === 0n, 'CRT construction gives universally shareable choice');
    }
    for (let t = s+1; t <= 125; ++t) {
      const end = Math.floor((num+den)*t/den);
      const second = lists(t,end), delta = t-s;
      const forced = new Set(first.filter(fs => fs.length === 1).map(fs => fs[0]));
      const blocker = second.find(fs => fs.every(p => forced.has(p) && delta%p !== 0));
      if (blocker) check(!directlyCompatible(first,second,delta),
        'an all-forced-but-unshareable factorization obstructs any choice');
      if (M <= 125n && BigInt(t) === tBig) check(directlyCompatible(first,second,delta),
        'small CRT construction independently satisfies all constraints');
    }
  }
}

function candidate(m, k, X) {
  for (let j = 1; j <= k; ++j) if (2*lcm(m,j) > X) return false;
  return true;
}
for (let k = 7; k <= 64; ++k) {
  let q = k;
  while (!prime(q)) --q;
  for (const X of [2*k*k, 2*k*k+2*k, 2*(k+1)*(k+1)-1]) {
    for (let m = k+1; m <= Math.floor(X/2); ++m) {
      check(lcm(2*m,2*q) === 2*lcm(m,q), 'even core compatibility reduction');
      if (m%2) check(lcm(m,2*q) === 2*lcm(m,q), 'odd core compatibility reduction');
      if (!candidate(m,k,X)) continue;
      const s = m-k;
      if (q > 2 && 4*q*(q-2) > X) {
        check(m%q !== 0 && 2*m*q <= X, 'large prime bounds every admissible offset');
      }
      for (let i = 0; i < k; ++i) {
        const j = k-i;
        if (2*m*j > X) {
          check(gcd(m,s+i) === gcd(m,j) && gcd(m,s+i) > 1,
            'over-threshold pair forces a common factor on the corresponding offset');
        }
      }
    }
  }
}
console.log('Chen-Dai compromise pairs: ' + assertions.toLocaleString('en-US') + ' exact assertions passed.');
