'use strict';
// Exact finite checks for FactorErdos786ProductLengthDensity.md.
let checks = 0;
function check(ok, why) { if (!ok) throw Error(why); ++checks; }
function g(a, b) { while (b) [a, b] = [b, a % b]; return a; }
function val(n, p) { let e = 0; while (n % p === 0) { n /= p; ++e; } return e; }
function mul(a) { return a.reduce((s, x) => s * x, 1n); }

// Model the lifting with deliberately overlapping candidate endpoint pools.
// The anchor product is the product of the given recurrent ratios.
const anchors = [ [2n], [2n, 3n], [2n, 5n, 9n], [3n, 4n, 7n], [2n, 3n, 4n, 5n] ];
for (const a of anchors) {
  const V = mul(a);
  for (let t = 1; t <= 5; ++t) {
    for (let b = 2n; b <= 19n; ++b) {
      const ratio = [];
      for (let i = 0; i < t - 1; ++i) {
        ratio.push(i % 2 ? [1n, b] : [b, 1n]);
      }
      ratio.push([V * mul(ratio.map(z => z[1])), mul(ratio.map(z => z[0]))]);
      const reduced = ratio.map(([u, v]) => { const d = g(u, v); return [u / d, v / d]; }).filter(([u, v]) => u !== v);
      check(mul(reduced.map(z => z[0])) === V * mul(reduced.map(z => z[1])), 'ratio factorization');
      for (let offset = 0n; offset <= 36n; ++offset) {
        const used = new Set(a), x = [], y = [];
        for (const [p, q] of reduced) {
          const hits = BigInt(a.length + 2 * reduced.length + 1);
          let chosen = false;
          for (let i = 1n; i <= hits; ++i) {
            const u = q * (offset + i), v = p * (offset + i);
            if (!used.has(u) && !used.has(v)) {
              used.add(u); used.add(v); x.push(u); y.push(v); chosen = true; break;
            }
          }
          // A forbidden endpoint can exclude up to two list positions, so
          // allow the full doubled bound if the tested short list did not suffice.
          if (!chosen) {
            for (let i = hits + 1n; i <= 2n * hits; ++i) {
              const u = q * (offset + i), v = p * (offset + i);
              if (!used.has(u) && !used.has(v)) {
                used.add(u); used.add(v); x.push(u); y.push(v); chosen = true; break;
              }
            }
          }
          check(chosen, 'availability after finitely many endpoints are forbidden');
        }
        check(used.size === a.length + 2 * reduced.length, 'all endpoints distinct');
        check(mul([...a, ...x]) === mul(y) && a.length + x.length > y.length, 'unequal product lengths');
      }
    }
  }
}

// Finite prime valuation law by exact count on complete residue periods.
const P = [2, 3, 5], range = 3, mod = P.reduce((s, p) => s * p ** range, 1);
const freq = new Map();
for (let n = 1; n <= mod; ++n) {
  const e = P.map(p => val(n, p));
  if (e.some(v => v >= range)) continue;
  const k = e.join();
  freq.set(k, (freq.get(k) || 0) + 1);
}
const triples = Array.from({ length: range ** 3 }, (_, i) => [i % range, Math.floor(i / range) % range, Math.floor(i / range ** 2)]);
for (const v of triples) {
  const expected = P.reduce((s, p, i) => s * (p - 1) * p ** (range - 1 - v[i]), 1);
  check(freq.get(v.join()) === expected, 'geometric CRT valuation counts');
}
for (let a = -4; a <= 4; ++a) for (let b = -4; b <= 4; ++b) for (let c = -4; c <= 4; ++c) {
  for (let m = 2; m <= 12; ++m) {
    const got = Array(m).fill(0), want = Array(m).fill(0);
    function key(e) { return ((a * e[0] + b * e[1] + c * e[2]) % m + m) % m; }
    for (const v of triples) {
      got[key(v)] += freq.get(v.join());
      want[key(v)] += P.reduce((s, p, i) => s * (p - 1) * p ** (range - 1 - v[i]), 1);
    }
    for (let j = 0; j < m; ++j) check(got[j] === want[j], 'same atom weights after projection');
  }
}

// A finite transport experiment: good primes preserve (v_5 mod 2, v_7 mod 2),
// which chooses the active color. Allow overlapping prime lists between colors.
const free = z => z % 2 !== 0 && z % 3 !== 0;
const cls = z => (val(z, 5) % 2) + 2 * (val(z, 7) % 2);
const ps = Array.from({ length: 700 }, (_, i) => i + 2).filter(p => {
  if (p < 11) return false;
  for (let d = 2; d * d <= p; ++d) if (p % d === 0) return false;
  return true;
});
const scaleSets = [[1, 2, 3, 4], [4, 2, 1, 3], [6, 5, 4, 3], [1, 1, 2, 2], [1, 5, 2, 6]];
for (const nums of scaleSets) {
  const D = 2;
  const w = nums.map(n => 60 * D / n);  // weights 60/tau_i
  check(w.every(Number.isInteger), 'integral weight scale');
  for (const Z of [6, 9, 18, 27, 54, 81, 108]) {
    const lists = nums.map(t => ps.filter(p => D * p > t * Z && 2 * D * p <= 3 * t * Z));
    for (let X = 125; X <= 3200; X += 47) {
      const L = Math.floor(X / Z);
      let total = 0, freeCount = 0, direct = 0;
      for (let z = 1; z <= L; ++z) {
        if (!free(z)) continue;
        ++freeCount;
        const cells = [];
        for (let i = 0; i < nums.length; ++i) {
          cells[i] = lists[i].filter(p => p * z * D <= nums[i] * X && cls(p * z) === i).length;
          total += w[i] * cells[i];
        }
        check(cells.filter(x => x > 0).length <= 1, 'at most one color per core and bin');
      }
      for (let i = 0; i < nums.length; ++i) {
        for (let n = 1; n * D <= nums[i] * X; ++n) {
          if (free(n) && cls(n) === i) direct += w[i] * lists[i].filter(p => n % p === 0).length;
        }
      }
      check(total === direct, 'divisor count reindexed by p times core');
      const cap = Math.max(...lists.map((q, i) => q.length * w[i]));
      check(total <= cap * freeCount, 'sharp per-bin capacity before PNT');
    }
  }
}
console.log('Exact assertions passed: ' + checks);
