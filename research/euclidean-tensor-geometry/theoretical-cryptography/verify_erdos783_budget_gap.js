'use strict';

// Exact finite checks for FactorErdos783SmallBudgetOptimalRate.md.
// Run: node verify_erdos783_budget_gap.js
// Only small integers are used as Numbers. Rational weights use BigInt
// in the first block and scaled integer units in the remaining blocks.

let count = 0;
function check(ok, label) {
  if (!ok) throw new Error(label);
  ++count;
}
function gcd(a, b) {
  while (b) [a, b] = [b, a % b];
  return a;
}
function choose(n, r) {
  if (r > n) return 0;
  let out = 1;
  for (let i = 1; i <= r; ++i) out = (out * (n - i + 1)) / i;
  return out;
}
function prime(p) {
  if (p < 2) return false;
  for (let d = 2; d * d <= p; ++d) if (p % d === 0) return false;
  return true;
}
function floor(n, d) { return Math.floor(n / d); }

let den = 1n;
const floorOfBest = [];
for (let N = 2; N <= 26; ++N) {
  den = den * BigInt(N) / BigInt(gcd(Number(den % BigInt(N)), N));
  const cof = (a) => den / BigInt(a);
  const a = [];
  floorOfBest.length = N + 1;
  floorOfBest.fill(N);
  function visit(first) {
    const div = Array(N + 1).fill(0);
    const mid = a.filter(p => prime(p) && p * p > N);
    const small = a.filter(x => x * x <= N);
    const nocube = a.filter(x => x * x * x > N);
    let survivors = 0, redundancy = 0, oneLess = 0;
    for (const x of a) for (let n = x; n <= N; n += x) ++div[n];
    for (let n = 1; n <= N; ++n) {
      survivors += Number(div[n] === 0);
      redundancy += Math.max(div[n] - 1, 0);
      const high = mid.filter(p => n % p === 0).length;
      const low = small.filter(x => n % x === 0).length;
      check(high <= 1 && Math.max(div[n] - 1, 0) >= high * low,
        'a disjoint upper cohort charges lower coincidences only once');
      oneLess += Math.max(nocube.filter(x => n % x === 0).length - 1, 0);
    }
    const mu = a.reduce((z, x) => z + cof(x), 0n);
    const round = a.reduce((z, x) => z + BigInt(N % x) * cof(x), 0n);
    check(BigInt(survivors - N) * den === -BigInt(N) * mu +
      round + BigInt(redundancy) * den, 'exact deficit');
    const fac = Array(a.length + 1).fill(0);
    function subsets(i, prod, r) {
      if (prod > N) return;
      if (i === a.length) { fac[r] += floor(N, prod); return; }
      subsets(i + 1, prod, r);
      subsets(i + 1, prod * a[i], r + 1);
    }
    subsets(0, 1, 0);
    for (let r = 0; r <= a.length; ++r) {
      const empirical = div.slice(1).reduce((z, d) => z + choose(d, r), 0);
      check(empirical === fac[r], 'factorial moment via products');
      let f = 1n;
      for (let k = 1; k <= r; ++k) f *= BigInt(k);
      check(BigInt(empirical) * f * den ** BigInt(r) <=
        BigInt(N) * mu ** BigInt(r), 'factorial moment upper bound');
    }
    let pairRedundancy = 0;
    for (let i = 0; i < nocube.length; ++i) for (let j = i + 1; j < nocube.length; ++j) {
      pairRedundancy += floor(N, nocube[i] * nocube[j]);
    }
    check(pairRedundancy === oneLess, 'exact overlap when no three moduli fit');
    for (let d = 2; d <= N; ++d) {
      if (mu <= cof(d)) floorOfBest[d] = Math.min(floorOfBest[d], survivors);
    }
    for (let x = first; x <= N; ++x) {
      if (a.every(y => gcd(x, y) === 1)) {
        a.push(x);
        visit(x + 1);
        a.pop();
      }
    }
  }
  visit(2);
  for (let d = 2; d <= N; ++d) {
    check(floorOfBest[d] === N - floor(N, d), 'exact reciprocal-budget minimum');
  }
}

// Integer formulation of {N/a} < 1/q. A full constituent interval
// (qN/(jq+1), N/j] has exactly the difference of the floors below.
for (let N = 2; N <= 240; ++N) {
  for (let q = 2; q <= 9; ++q) {
    const direct = Array(N + 1).fill(0);
    for (let a = 1; a <= N; ++a) {
      const j = floor(N, a);
      const good = (N % a) * q < a;
      const inInterval = a * (j * q + 1) > N * q && a * j <= N;
      check(good === inInterval, 'strict fractional-part interval endpoints');
      if (good) ++direct[j];
    }
    for (let j = 1; j <= N; ++j) {
      check(direct[j] === floor(N, j) - floor(N * q, j * q + 1),
        'counting integers by fractional-part intervals');
    }
  }
}

// Verify stochastic dominance and both product comparisons over every
// integral submeasure of several atomic measures. Splitting a weight
// into units permits fractional inclusion of an endpoint atom.
for (const pos of [[2,3,5,8], [2,5,6,11,23], [3,7,10,12,15]]) {
  for (const cap of [[2,1,3,2,4], [1,4,2,3,1], [3,2,3,1,2]]) {
    const n = pos.length;
    const u = Array(n).fill(0);
    function compare(k, m) {
      if (k < n) {
        for (let t = 0; t <= cap[k]; ++t) {
          u[k] = t;
          compare(k + 1, m + t);
        }
        return;
      }
      const v = Array(n).fill(0);
      let rest = m;
      for (let i = n - 1; i >= 0; --i) {
        v[i] = Math.min(rest, cap[i]);
        rest -= v[i];
      }
      check(rest === 0, 'suffix uses the prescribed mass');
      for (let i = 0; i <= n; ++i) {
        const su = u.slice(i).reduce((z, a) => z + a, 0);
        const sv = v.slice(i).reduce((z, a) => z + a, 0);
        const sc = cap.slice(i, n).reduce((z, a) => z + a, 0);
        check(sv === Math.min(m, sc) && sv >= su, 'right-tail dominance');
      }
      for (const b of pos.flatMap(s => pos.map(t => s * t))) {
        let uu = 0, uv = 0, vv = 0;
        for (let i = 0; i < n; ++i) for (let j = 0; j < n; ++j) {
          if (pos[i] * pos[j] <= b) {
            uu += u[i] * u[j];
            uv += u[i] * v[j];
            vv += v[i] * v[j];
          }
        }
        check(uu >= uv && uv >= vv, 'replacing each factor lowers decreasing product kernel');
      }
    }
    compare(0, 0);
  }
}

// The rescaled triangle after translation has coordinates i,j >= 0
// with i+j <= h. Check the lattice count and the unordered correction.
for (let h = 1; h <= 200; ++h) {
  let ordered = 0, unordered = 0, diagonal = 0;
  for (let i = 0; i <= h; ++i) {
    for (let j = 0; i + j <= h; ++j) {
      ++ordered;
      unordered += Number(i < j);
      diagonal += Number(i === j);
    }
  }
  check(2 * ordered === (h + 1) * (h + 2), 'triangle lattice area normalization');
  check(ordered === 2 * unordered + diagonal, 'ordered versus unordered pairs');
}
console.log('Small coprime sieve: ' + count.toLocaleString('en-US') + ' exact assertions passed.');
