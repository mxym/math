'use strict';
// Exact small cases for FactorErdos18BranchingDivisorSums.md.
let checks = 0;
function check(ok, label) { if (!ok) throw Error(label); ++checks; }
function pop(x) { let n = 0; for (; x; x &= x - 1) ++n; return n; }
const vals = n => Array.from({ length: n }, (_, i) => i);

// Interpret a strategy as an alternating game through a low-bit-first trie.
function win(inD, width, free, prefix = 0, pos = 0) {
  if (pos === width) return inD(prefix);
  const try0 = win(inD, width, free, prefix, pos + 1);
  if (free & (1 << pos)) return try0 && win(inD, width, free, prefix | (1 << pos), pos + 1);
  return try0 || win(inD, width, free, prefix | (1 << pos), pos + 1);
}
// Independent family computation via union/intersection on the actual sets.
function maskList(ds, width) {
  if (!width) return new Set(ds.length ? [0] : []);
  const left = maskList(ds.filter(d => !(d & 1)).map(d => d >> 1), width - 1);
  const right = maskList(ds.filter(d => d & 1).map(d => d >> 1), width - 1);
  const out = new Set([...left, ...right].map(m => m << 1));
  for (const m of left) if (right.has(m)) out.add((m << 1) + 1);
  return out;
}
for (let l = 0; l <= 4; ++l) {
  const space = 1 << l;
  for (let dm = 0; dm < (1 << space); ++dm) {
    const ds = vals(space).filter(x => dm & (1 << x));
    const family = maskList(ds, l);
    check(family.size === pop(dm), 'number of masks equals the number of leaves');
    for (let f = 0; f < space; ++f) {
      check(family.has(f) === win(x => !!(dm & (1 << x)), l, f), 'both definitions of controllability');
    }
  }
}

function factorial(x) { let z = 1n; for (let n = 2n; n <= BigInt(x); ++n) z *= n; return z; }
function maxMask(ds, l) {
  return [...maskList(ds, l)].reduce((b, a) => pop(a) > pop(b) ? a : b, 0);
}
for (let k = 7; k <= 13; ++k) {
  const m = 12, fact = factorial(m), cap = factorial(m + 2 * k);
  for (let pattern = 0; pattern < 4; ++pattern) {
    const bank = [];
    for (let j = 0; j < k; ++j) {
      const dist = Math.min(j, k - 1 - j);
      if (dist < 2) { bank.push({ a: j, l: 1, D: [0, 1], I: 1 }); continue; }
      const l = 2 ** Math.floor(Math.log2(dist));
      const D = vals(1 << l).filter(x => !x || (fact % BigInt(x) === 0n &&
        (x === 1 || ((x + pattern * x * x) % 5 !== 4))));
      const I = maxMask(D, l);
      check(I > 0, 'nonempty marked levels at each test scale');
      const b = vals(l).filter(i => (I & (1 << i)) !== 0);
      const a = j - b[(j + pattern) % b.length];
      check(a >= 0 && a + l <= k, 'both-end height restriction');
      bank.push({ a, l, D, I });
      if (j % 4 === 3) bank.push({ a, l, D, I }); // intentional repeats and overlapping carries
    }
    for (let target = 0; target < (1 << k); ++target) {
      const states = bank.map(v => ({...v, prefix: 0}));
      let carry = 0;
      for (let j = 0; j < k; ++j) {
        const active = states.filter(v => v.a <= j && j < v.a + v.l);
        const controller = active.find(v => v.I & (1 << (j - v.a)));
        check(Boolean(controller), 'full coverage of output bit positions');
        let s = carry;
        for (const v of active) {
          if (v === controller) continue;
          const pos = j - v.a;
          if (!(v.I & (1 << pos))) {
            if (!win(x => v.D.includes(x), v.l, v.I, v.prefix, pos + 1)) {
              v.prefix |= 1 << pos; ++s;
              check(win(x => v.D.includes(x), v.l, v.I, v.prefix, pos + 1), 'forced-bit legal continuation');
            }
          }
        }
        const tBit = (target >> j) & 1;
        if ((s & 1) !== tBit) {
          controller.prefix |= 1 << (j - controller.a);
          ++s;
        }
        check((s & 1) === tBit, 'local carry parity');
        carry = s >> 1;
      }
      let sum = 1n << BigInt(k); // positive even at residue zero
      for (const v of states) {
        check(v.D.includes(v.prefix), 'strategy finishes at allowed digit');
        if (!v.prefix) continue;
        const term = BigInt(v.prefix) << BigInt(v.a);
        check(term < (1n << BigInt(k)) && cap % term === 0n, 'short positive factorial divisor');
        sum += term;
      }
      const q = 1n << BigInt(k);
      check(sum > 0n && sum <= BigInt(bank.length + 1) * q && sum % q === BigInt(target), 'actual positive residue realization');
    }
  }
}

// Binary carrying within fixed odd parts preserves exact sums and distinctness.
let rng = 781321234;
function random() { rng = ((rng ^ (rng << 13)) >>> 0); rng = ((rng ^ (rng >>> 17)) >>> 0); rng = ((rng ^ (rng << 5)) >>> 0); return rng; }
const odds = [1n, 3n, 5n, 7n, 9n, 11n];
const divisorsAllowed = (1n << 12n) * 3n * 3n * 5n * 7n * 11n;
for (let z = 0; z < 3000; ++z) {
  const w = random() % 62 + 1, G = new Map();
  let total = 0n;
  for (let i = 0; i < w; ++i) {
    const odd = odds[random() % odds.length], pow = 1n << BigInt(random() % 13);
    G.set(odd, (G.get(odd) || 0n) + pow); total += odd * pow;
  }
  const packed = [];
  for (const [odd, group] of G) {
    for (let b = 0n; (1n << b) <= group; ++b) {
      if ((group >> b) & 1n) packed.push(odd << b);
    }
  }
  const cap = divisorsAllowed << BigInt(31 - Math.clz32(w));
  check(new Set(packed).size === packed.length && packed.length <= w, 'binary carrying count and uniqueness');
  check(packed.reduce((s, t) => s + t, 0n) === total, 'carrying preserves value');
  for (const term of packed) check(cap % term === 0n, 'carrying requires at most floor(log_2 w) extra factors of two');
}
console.log('Exact assertions passed: ' + checks);
