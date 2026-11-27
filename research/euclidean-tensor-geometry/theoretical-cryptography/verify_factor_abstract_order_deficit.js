"use strict";

// Exact finite checks in predetermined cyclic-size and prime-pair toys.
// No input and no order or exponent computations.
let checks = 0;
function check(yes, label) {
  checks++;
  if (!yes) throw Error(label);
}
function gcd(z, w) {
  while (w) [z, w] = [w, z % w];
  return z < 0n ? -z : z;
}
function F(n, d = 1n) {
  if (d === 0n) throw Error("zero denominator");
  const g = gcd(n, d) * (d < 0n ? -1n : 1n);
  return [n / g, d / g];
}
const plus = ([a, b], [c, d]) => F(a * d + b * c, b * d);
const sub = ([a, b], [c, d]) => F(a * d - b * c, b * d);
const mul = ([a, b], [c, d]) => F(a * c, b * d);
const div = ([a, b], [c, d]) => F(a * d, b * c);
const eq = (a, b) => a[0] === b[0] && a[1] === b[1];
const le = ([a,b], [c,d]) => a * d <= b * c;
const zero = F(0n), one = F(1n);
function ellPower(ell, a) { return BigInt(ell) ** BigInt(a); }
function unscaled(ell, t, k, a, b) {
  if (a < 0 || b < 0 || Math.max(a,b) < k) return zero;
  return F(1n, ellPower(ell, t * Math.max(0, k - Math.abs(a-b))));
}
function coefficient(ell,t,k,a,b) {
  return plus(sub(sub(unscaled(ell,t,k,a,b), unscaled(ell,t,k,a-1,b)),
                  unscaled(ell,t,k,a,b-1)), unscaled(ell,t,k,a-1,b-1));
}
function closed(ell,t,k) {
  const p = BigInt(ell), r = F(1n,ellPower(ell,t+1)), rr = F(1n,ellPower(ell,(t+1)*k));
  const sqden = sub(one, F(1n,p*p));
  const aa = mul(F(2n), plus(F(p,p-1n), div(sub(div(r,sub(one,r)),F(1n,p-1n)),sqden)));
  const bb = div(plus(one,r), mul(sub(one,r),sqden));
  return sub(mul(aa,rr),mul(bb,mul(rr,rr)));
}
function sizeMass(ell,a) {
  return a === 0 ? F(BigInt(ell-2),BigInt(ell-1)) : F(1n,ellPower(ell,a));
}

for (const ell of [2,3,5,7,11]) for (let t = 1; t <= 4; t++) {
  for (let k = 1; k <= 5; k++) {
    let truncated = zero;
    const cap = 10;
    for (let a = 0; a <= cap; a++) for (let b = 0; b <= cap; b++) {
      const local = mul(F(1n,ellPower(ell,t*k)), unscaled(ell,t,k,a,b));
      truncated = plus(truncated, mul(local,mul(sizeMass(ell,a),sizeMass(ell,b))));
    }
    const got = closed(ell,t,k);
    const omitted = F(2n,BigInt(ell-1)*ellPower(ell,cap));
    check(le(truncated,got) && le(sub(got,truncated),omitted),
          "closed local survivor between truncated sum and its exact tail bound");

    for (let a = 0; a <= 5; a++) for (let b = 0; b <= 5; b++) {
      let telescoped = zero;
      for (let i = 0; i <= a; i++) for (let j = 0; j <= b; j++) {
        const c = coefficient(ell,t,k,i,j);
        if (Math.max(i,j) < k) check(eq(c,zero), "support condition");
        telescoped = plus(telescoped,c);
      }
      check(eq(telescoped,unscaled(ell,t,k,a,b)), "two-dimensional telescoping");

      // Count residues in each abstract cyclic exponent block satisfying a bound.
      const limit = Math.max(a,b)-k;
      const local = mul(F(1n,ellPower(ell,t*k)), unscaled(ell,t,k,a,b));
      if (limit < 0) {
        check(eq(local,zero), "unattainable cyclic deficit");
      } else {
        const prodCount = ellPower(ell,(Math.min(a,limit)+Math.min(b,limit))*t);
        check(eq(local,F(prodCount,ellPower(ell,(a+b)*t))), "cyclic sampling law");
      }
    }
  }
}

const primes = [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];
function val(n,p) {
  let a = 0;
  while (!(n % p)) { n /= p; a++; }
  return a;
}
for (const X of [10,15,23,31,45]) {
  const pool = primes.filter(p => X < p && p <= 2*X);
  const M = BigInt(pool.length);
  const denominator = M*(M-1n);
  const hits = n => BigInt(pool.filter(p => (p-1)%n===0).length);
  for (let a=1; a<=20; a++) for(let b=1; b<=20; b++) {
    let direct = 0n;
    for (const p of pool) for (const q of pool) {
      if (p !== q && (p-1)%a===0 && (q-1)%b===0) direct++;
    }
    const lcm = Number(BigInt(a*b)/gcd(BigInt(a),BigInt(b)));
    check(direct===hits(a)*hits(b)-hits(lcm),"distinct pair count including removed diagonal");
  }
  for (const specification of [[[2,1]],[[2,2]],[[3,1]],[[2,1],[3,1]],[[2,2],[3,1]]]) {
    let direct = zero;
    for (const p of pool) for (const q of pool) if (p !== q) {
      const terms = specification.map(([ell,k]) => unscaled(ell,2,k,val(p-1,ell),val(q-1,ell)));
      direct = plus(direct,terms.reduce(mul,one));
    }
    let cumulative = [[1,1,one]];
    for (const [ell,k] of specification) {
      const next = [];
      const top = Math.max(...pool.map(p => val(p-1,ell)));
      for (const [a,b,c] of cumulative) for(let i=0;i<=top;i++) for(let j=0;j<=top;j++) {
        const cc = coefficient(ell,2,k,i,j);
        if (!eq(cc,zero)) next.push([a*ell**i,b*ell**j,mul(c,cc)]);
      }
      cumulative = next;
    }
    let viaTable = zero;
    for (const [a,b,c] of cumulative) {
      const ell = Number(BigInt(a*b)/gcd(BigInt(a),BigInt(b)));
      viaTable = plus(viaTable,mul(c,F(hits(a)*hits(b)-hits(ell))));
    }
    check(eq(div(direct,F(denominator)),div(viaTable,F(denominator))),
          "actual bivariate divisibility comparison before common scale factor");
  }
}
console.log("Passed " + checks + " exact toy identities and inequalities.");
