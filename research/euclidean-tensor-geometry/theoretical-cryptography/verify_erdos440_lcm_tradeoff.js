'use strict';

// Finite checks for FactorErdos440LCMTradeoff.md.
// Run with Node.js. All Number arithmetic below is on small integers;
// rational inequalities in the weighted-capacity check are scaled by BigInt.

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
function ceilDiv(a, b) { return Math.floor((a + b - 1) / b); }
function isqrt(n) {
  const m = Math.floor(Math.sqrt(n));
  check(m * m <= n && (m + 1) * (m + 1) > n, 'checked integer square root');
  return m;
}
function band(a, b, T) {
  const j = ceilDiv(b * b, T * T);
  return a * a >= (j - 1) * T * T ? j : 0;
}
for (let T = 2; T <= 30; ++T) {
  for (let a = 1; a <= 110; ++a) {
    for (let b = a + 1; b <= 111; ++b) {
      const g = b - a, j = band(a, b, T), d = lcm(a, b);
      check(g * d >= a * b, 'integer LCM gap constraint');
      if (j) {
        check((j - 1) * T * T < a * b && b * b <= j * T * T,
          'strict internal-band inequality');
        check(g * ceilDiv(d, T * T) >= j, 'edge can pay its normalized capacity');
        if (d <= T * T) check(g >= j, 'peak edge pays at least one');
      }
    }
  }
}

function describe(a, T) {
  return a.slice(1).map((v, i) => {
    const u = a[i];
    return { u, v, g: v - u, d: lcm(u, v), j: band(u, v, T) };
  });
}
for (const T of [2, 4, 7, 11]) {
  for (const K of [2, 4, 6]) {
    const W = Math.max(20, ceilDiv(13 * 13, T * T), K + 1);
    let den = 1n;
    for (let j = 1; j <= W; ++j) {
      den = den * BigInt(j) / BigInt(gcd(j, Number(den % BigInt(j))));
    }
    const denBy = j => den / BigInt(j);
    const charge = z => {
      if (z <= 1) return den;
      let r = 0n;
      for (let k = z; k <= K; ++k) r += denBy(k) - denBy(k + 1);
      const exact = z <= K ? denBy(z) - denBy(K + 1) : 0n;
      check(r === exact, 'finite threshold weights telescope exactly');
      return r;
    };
    for (let mask = 0; mask < (1 << 13); ++mask) {
      const a = [];
      for (let j = 0; j < 13; ++j) if (mask & (1 << j)) a.push(j + 1);
      const edges = describe(a, T);
      let weightedCost = 0n, gapCapacity = 0n;
      for (const {u, v, g, j, d} of edges) {
        if (!j) continue;
        weightedCost += charge(ceilDiv(d, T * T));
        gapCapacity += BigInt(g) * denBy(j);
        // Both endpoints are in this band, with zero-length overlaps permitted.
        check(u < v && v * v <= j * T * T, 'kept edge has the claimed upper endpoint');
      }
      check(weightedCost <= gapCapacity, 'multiscale weighted budget on all kept edges');
      for (let U = 1; U < 14; U *= 2) {
        const matching = edges.filter(e => U <= e.u && e.u < 2 * U && e.d <= K*T*T);
        check((matching.length - 1) * U <= K * T * T, 'dyadic tail packing');
      }
    }
  }
}

// Build bounded stages and certify each witness as an actual adjacent pair.
// r is supplied as a rational cutoff, independently of the asymptotic curve.
for (const T of [50, 111, 325, 800]) {
  for (const R of [3, 5, 9]) {
    for (const [num, den, rNum, rDen] of [[0,1,3,2], [1,8,8,3], [1,2,7,4], [4,5,10,9]]) {
      let cells = 0;
      const H = isqrt(T);
      const B = R*T;
      const r = Math.floor(rNum*T/rDen);
      const a = [];
      for (let n = 1; n <= T; ++n) a.push(n);
      const peak = [], dense = [];
      function piece(lo, hi, j, denseMode) {
        for (let q = lo; q <= hi; q += H) {
          ++cells;
          const end = Math.min(q+H-1,hi);
          const size = end-q+1;
          const len = denseMode ? Math.floor(num*size/den) : 0;
          for (let n = q; n < q+len; ++n) {
            a.push(n);
            if (n > q) dense.push([n-1,n]);
          }
          if (denseMode) {
            check(den*(len-1) >= num*size-2*den, 'dense cell rounding');
          }
          let last, found = 0;
          const first = ceilDiv(q+len,j)*j;
          for (let n = first; n <= end; n += j) {
            a.push(n);
            if (last !== undefined) {
              peak.push([last,n]);
              ++found;
            }
            last = n;
          }
          check(j*found >= (size-len)-2*j, 'sparse cell rounding');
        }
      }
      for (let j = 2; j <= R*R; ++j) {
        const lo = isqrt((j-1)*T*T)+1, hi = isqrt(j*T*T);
        piece(lo,Math.min(hi,r),j,false);
        piece(Math.max(lo,r+1),hi,j,true);
      }
      for (let n = B+1; n <= B+2*T; ++n) a.push(n);
      const adj = new Map(a.slice(1).map((n,i) => [a[i],n]));
      for (let i = 1; i < a.length; ++i) check(a[i-1] < a[i], 'stage is strictly increasing');
      const used = new Set();
      for (const [u,v] of peak) {
        check(adj.get(u) === v && !used.has(u), 'each sparse witness is truly adjacent and unique');
        check(lcm(u,v) <= T*T, 'sparse witness contributes at peak');
        used.add(u);
      }
      for (const [u,v] of dense) {
        check(adj.get(u) === v && !used.has(u), 'distinct dense adjacent witness');
        check(lcm(u,v) === u*v && u > r, 'dense threshold and correct side of cutoff');
        used.add(u);
      }
      let idx = 0;
      for (let x = T; x <= B; ++x) {
        while (idx < dense.length && dense[idx][1] <= x) ++idx;
        check(den*idx >= num*Math.max(0,x-r)-den*(2*cells+H+1),
          'uniform dense cutoff estimate');
      }
      const ds = a.slice(1).map((v,i) => lcm(a[i],v)).sort((x,y) => x-y);
      let ptr = 0;
      while (ptr < ds.length && ds[ptr] <= B*B) ++ptr;
      const old = ptr;
      for (let x = B; x <= B+2*T; ++x) {
        while (ptr < ds.length && ds[ptr] <= x*x) ++ptr;
        check(ptr-old >= x-B-1, 'dense bridge preserves previously counted pairs');
      }
    }
  }
}
console.log('Consecutive LCM trade-off: ' + assertions.toLocaleString('en-US') + ' exact assertions passed.');
