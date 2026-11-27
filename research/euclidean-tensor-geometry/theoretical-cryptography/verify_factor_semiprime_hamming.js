"use strict";

// Exact checks on predetermined finite residue sets and small toy products.
// No input and no factor computation.
let checks = 0;
function check(condition, label) {
  checks++;
  if (!condition) throw Error(label);
}
function mod(a, m) { return ((a % m) + m) % m; }
function badCount(ell, d) { return d % ell ? 3 * ell - 2 : 2 * ell - 1; }
const small = [5,7,11,13,17,19,23,29,31];
for (const ell of small) for (let d = -ell; d <= ell; d++) {
  let found = 0;
  let inv = 1;
  while (mod(inv * 67, ell) !== 1) inv++;
  for (let a = 0; a < ell; a++) for (let b = 0; b < ell; b++) {
    const s = mod((a*b-d)*inv,ell);
    const bad = a === 0 || b === 0 || s === 0;
    check(bad === (a === 0 || b === 0 || mod(a*b-d,ell) === 0), "third-entry residues");
    found += bad;
  }
  check(found === badCount(ell,d), "one-prime local density");
}
for (const [p,q] of [[5,7],[5,11],[7,13],[11,17]]) {
  const m = p*q;
  for (const d of [-20,-13,-1,1,2,5,7,11,13,20,35,385]) {
    let count = 0;
    for (let a = 0; a < m; a++) for (let b = 0; b < m; b++) {
      if (a*b*(a*b-d) % m === 0) count++;
    }
    check(count === badCount(p,d)*badCount(q,d), "two-prime CRT density");
  }
}

const moduli = [1];
for (const p of [5,7,11,13]) moduli.push(...moduli.map(m => m*p));
const orders = new Map([[1,1]]);
for (const m of moduli.slice(1)) {
  let t = 1, v = 2 % m;
  while (v !== 1) {
    v = 2*v % m;
    t++;
    if (t > m) throw Error("finite toy order");
  }
  orders.set(m,t);
}
for (let B = 2; B <= 14; B++) for (let a = -50; a <= 50; a++) {
  for (const sign of [-1,1]) {
    for (const m of moduli) {
      const J = [];
      for (let j = 0; j < B; j++) {
        const d = a+sign*2**j;
        if (d && d % m === 0) J.push(j);
      }
      const t = orders.get(m);
      check(J.length <= Math.ceil(B/t)+1, "period gives bounded number of candidates");
      for (const j of J) check((j-J[0])%t === 0, "one class of exponents");
    }
  }
}

const toy = [29,31,37,41,43,47,53];
const products = toy.flatMap((a,i)=>toy.slice(i+1).map(b=>a*b));
check(new Set(products).size === products.length, "distinct toy products");
const differences = new Map();
for (const n of products) for (const m of products) if (n!==m) {
  const d = n-m;
  differences.set(d,(differences.get(d)||0)+1);
  let sum = 0, changes = 0;
  for (let j = 0; j < 14; j++) {
    const u = ((n>>j)&1)-((m>>j)&1);
    sum += u * (2 ** j);
    if (u) changes++;
  }
  check(sum === d && changes > 0, "signed binary shift for distinct products");
}
for (const [d, value] of differences) {
  check(differences.get(-d) === value, "ordered-shift symmetry");
}
console.log("Passed " + checks + " exact toy identities and inequalities.");
