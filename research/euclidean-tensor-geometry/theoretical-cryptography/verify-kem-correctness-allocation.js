'use strict';
// Exact arithmetic on synthetic Bernoulli models only; no cryptographic data.
const d = 4n;
function* ordered(k, start = 0, a = []) {
  if (k === 0) { yield a; return; }
  for (let q = start; q <= 4; q++) yield* ordered(k - 1, q, [...a, q]);
}
function* perms(a) {
  if (!a.length) { yield []; return; }
  const used = new Set();
  for (let i = 0; i < a.length; i++) {
    if (used.has(a[i])) continue;
    used.add(a[i]);
    for (const t of perms(a.slice(0, i).concat(a.slice(i + 1)))) yield [a[i], ...t];
  }
}
function* loads(k, t, a = []) {
  if (k === 0) { if (t === 0) yield a; return; }
  for (let q = 0; q <= t; q++) yield* loads(k - 1, t - q, [...a, q]);
}
const zero = n => Array(n).fill(0n);
function conv(a, b) {
  const c = zero(a.length + b.length - 1);
  for (let i = 0; i < a.length; i++)
    for (let j = 0; j < b.length; j++) c[i + j] += a[i] * b[j];
  return c;
}
function poly(ns, ps) {
  let a = [1n];
  for (let i = 0; i < ns.length; i++)
    for (let j = 0; j < ns[i]; j++) a = conv(a, [d - BigInt(ps[i]), BigInt(ps[i])]);
  return a;
}
function add(a, b, c = 1n) {
  for (let i = 0; i < b.length; i++) a[i] += c * b[i];
}
let checked = 0, nonzero = 0, stops = 0;
for (let k = 2; k <= 4; k++) for (const orbit of ordered(k)) {
  const pp = [...perms(orbit)];
  for (let n = 2; n <= 8; n++) for (const ns of loads(k, n)) {
    const [a, b, ...other] = ns;
    if (a < b || b < 1) continue;
    const delta = zero(n + 1), squared = zero(n + 1);
    for (const ps of pp) {
      add(delta, poly([a + 1, b - 1, ...other], ps));
      add(delta, poly(ns, ps), -1n);
      const factors = zero(n - 1);
      for (let j = 0; j <= a - b; j++)
        add(factors, poly([b - 1 + j, a - 1 - j, ...other], ps));
      add(squared, conv([1n, -2n, 1n], factors), BigInt((ps[0] - ps[1]) ** 2));
    }
    // Both sides have denominator d^n times the orbit size, aside from 1/2 in (1).
    if (delta.some((v, i) => 2n * v !== squared[i])) throw Error('factorization');
    if (delta.some(v => v !== 0n)) nonzero++;
    for (let t = 0; t <= n; t++) {
      const change = delta.slice(t + 1).reduce((s, v, r) => s + BigInt(r + 1) * v, 0n);
      if (change < 0n) throw Error('convex order');
      stops++;
    }
    checked++;
  }
}
console.log({checked, nonzero, stops});
