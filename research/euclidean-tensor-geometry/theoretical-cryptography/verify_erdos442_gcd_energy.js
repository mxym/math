'use strict';
// Exact finite stress tests for FactorErdos442GcdEnergy.md. No floating point.
let checks = 0;
function check(ok, what) { if (!ok) throw Error(what); ++checks; }
const fact = n => n < 2 ? 1n : BigInt(n) * fact(n - 1);
const pow = (a, n) => a ** BigInt(n);
function gcd(a, b) { while (b) [a, b] = [b, a % b]; return a; }
function pop(a) { let r = 0; for (; a; a &= a - 1) ++r; return r; }

function subsets(p) {
  const products = [1n], phi = [1n];
  for (const x of p) {
    products.push(...products.map(n => n * x));
    phi.push(...phi.map(n => n * (x - 1n)));
  }
  return { products, phi };
}

// Arbitrary, possibly non-squarefree sets. Weights are 1/n scaled by 27720.
const primes = [2, 3, 5, 7, 11], cap = 12, scale = 27720n;
const phiSmall = Array.from({ length: cap + 1 }, (_, n) => {
  let a = 0n;
  for (let i = 1; i <= n; ++i) if (gcd(BigInt(n), BigInt(i)) === 1n) ++a;
  return a;
});
const omega = Array.from({ length: cap + 1 }, (_, n) => primes.filter(p => n % p === 0).length);
const { products: sf, phi: psf } = subsets(primes.map(BigInt));
const trials = [ [1n, 5n], [2n, 3n], [1n, 1n] ];
for (let mask = 1; mask < (1 << cap); ++mask) {
  const set = Array.from({ length: cap }, (_, i) => i + 1).filter(n => mask & (1 << (n - 1)));
  const w = n => scale / BigInt(n);
  const v = d => set.reduce((s, n) => n % d === 0 ? s + w(n) : s, 0n);
  let square = 0n, pair = 0n;
  for (let d = 1; d <= cap; ++d) square += phiSmall[d] * v(d) ** 2n;
  for (const a of set) for (const b of set) pair += w(a) * w(b) * gcd(BigInt(a), BigInt(b));
  check(square === pair, 'Gauss, diagonal included');
  for (const [a, b] of trials) {
    // t=a/b. Scale both divisor-moment expressions by b to maximum rank.
    const R = primes.length;
    const moment = set.reduce((s, n) => s + w(n) * pow(a + b, omega[n]) * pow(b, R - omega[n]), 0n);
    let dv = 0n;
    for (let i = 0; i < sf.length; ++i) {
      if (sf[i] > BigInt(cap)) continue;
      const l = pop(i);
      dv += v(Number(sf[i])) * pow(a, l) * pow(b, R - l);
    }
    check(moment === dv, 'divisor-moment expansion');
    const numer = primes.reduce((z, p) => z * (b * b * BigInt(p - 1) + a * a), 1n);
    check(moment * moment * psf[psf.length - 1] <= pair * numer, 'all-rank Cauchy--Schwarz');
  }
}

const p = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n];
const { products, phi } = subsets(p);
function layer(mask, k) {
  const den = products[mask];
  let h = 0n, u = 0n, u2 = 0n;
  for (let a = mask; a; a &= a - 1) {
    const b = a & -a;
    u += den / products[b]; u2 += (den / products[b]) ** 2n;
  }
  const coord = new Map();
  for (let sub = mask;; sub = (sub - 1) & mask) {
    if (pop(sub) === k) {
      const w = den / products[sub];
      h += w;
      for (let d = sub;; d = (d - 1) & sub) {
        coord.set(d, (coord.get(d) || 0n) + w);
        if (!d) break;
      }
    }
    if (!sub) break;
  }
  const ranks = Array(k + 1).fill(0n);
  for (const [d, z] of coord) ranks[pop(d)] += phi[d] * z * z;
  return { den, h, u, u2, ranks, norm: ranks.reduce((a, b) => a + b, 0n) };
}
const layers = new Map();
function L(m, k) {
  const key = (m << 4) + k;
  if (!layers.has(key)) layers.set(key, layer(m, k));
  return layers.get(key);
}
for (let m = 1; m < products.length; ++m) {
  for (let k = 1; k <= pop(m) + 1; ++k) {
    const { den, h, u, u2, ranks } = L(m, k);
    const denPow = pow(den, k - 1);
    check(fact(k) * h * denPow <= pow(u, k), 'ordered upper');
    if (k >= 2) check(fact(k) * h * denPow >= pow(u, k) - BigInt(k * (k - 1) / 2) * pow(u, k - 2) * u2, 'tuple collision lower');
    for (let d = 0; d <= k; ++d) {
      check(ranks[d] * fact(d) * fact(k - d) ** 2n * pow(den, Math.max(2 * k - d - 2, 0))
            <= pow(u, 2 * k - d) * pow(den, Math.max(2 - 2 * k + d, 0)), 'rank norm bound');
    }
    const pcut = m & (m - 1);
    const lp = L(pcut, k), retained = lp.h * (den / lp.den), up = lp.u * (den / lp.den);
    check(h >= retained, 'subset monotonicity');
    // h and retained use denominator den; u and up also use denominator den.
    check((h - retained) * fact(k - 1) * denPow <= (u - up) * pow(u, k - 1), 'loss of a marked prime');
  }
}
for (let m = 0; m < products.length; ++m) {
  const q = (products.length - 1) ^ m;
  for (let j = 0; j <= Math.min(4, pop(m)); ++j) {
    for (let r = 0; r <= Math.min(4, pop(q)); ++r) {
      const a = L(m, j), b = L(q, r), den = a.den * b.den;
      const f = [];
      for (let t = 0; t < products.length; ++t) {
        if (pop(t & m) === j && pop(t & q) === r) f.push(products[t]);
      }
      const h = f.reduce((s, n) => s + den / n, 0n);
      let norm = 0n;
      const v = new Map();
      for (const n of f) {
        const t = products.indexOf(n);
        for (let d = t;; d = (d - 1) & t) {
          v.set(d, (v.get(d) || 0n) + den / n);
          if (!d) break;
        }
      }
      for (const [d, z] of v) norm += phi[d] * z * z;
      check(h === a.h * b.h, 'box mass');
      check(norm === a.norm * b.norm, 'tensor norm');
    }
  }
}
for (let r = 2; r <= 12; ++r) {
  for (let k = 1; k <= 220; ++k) {
    const a = pow(BigInt(k), r - 1);
    let t = 1n;
    while (pow(t, r) < a) ++t;
    for (let u = 0n; u <= 240n; ++u) {
      // t is the ceiling of k^(1-1/r); exact bound with slack 2^r.
      check(t * pow(u + 1n, r - 1) <= pow(2n, r) * (a + pow(u, r)), 'stage transition');
    }
  }
}
console.log('Exact assertions passed: ' + checks);
