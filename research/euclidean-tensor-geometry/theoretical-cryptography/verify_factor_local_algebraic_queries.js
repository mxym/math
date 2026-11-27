"use strict";

// All inputs and output pairs are built from these explicit toy primes.
// No input number is factored, and no data is read from outside this script.
const primes = [37n, 41n, 43n, 47n, 53n, 59n, 61n, 67n, 71n, 73n];
const M = primes.length;
const products = [];
for (let i = 0; i < M; i++)
  for (let j = i + 1; j < M; j++)
    products.push({a: primes[i], b: primes[j], x: primes[i] * primes[j]});

let checks = 0, graphs = 0, curves = 0, slices = 0, graphEdges = 0;
function ok(b, msg) { checks++; if (!b) throw Error(msg); }
function abs(x) { return x < 0n ? -x : x; }
function gcd(a,b) {
  a = abs(a); b = abs(b);
  while (b) [a,b] = [b,a%b];
  return a;
}
function evalPoly(P, x, y) {
  let s = 0n;
  for (const [i,j,c] of P) s += c * x**BigInt(i) * y**BigInt(j);
  return s;
}
function degree(P) { return Math.max(...P.map(([i,j]) => i+j)); }
function perm(k, step) {
  return primes.map((_,i) => primes[(k+step*i)%M]);
}

// Rank-two charts: irreducible lines and Y^2 + uX + v, u != 0.
for (let k = 0; k < 18; k++) {
  const A = perm(k,[1,3,7,9][k%4]), B = perm(k+3,[9,7,3,1][k%4]);
  for (let i = 0; i < M; i++) {
    const j = (i+2+k)%M;
    const x = primes[i]*primes[j], y = A[i]*B[j], u = BigInt(k+1);
    for (let a = 1; a <= 2; a++) {
      const P = [[0,a,1n],[1,0,u],[0,0,-(y**BigInt(a)+u*x)]];
      const d = degree(P);
      const E = primes.map((p,l) => primes.map((q,r) =>
        l!==r && A[l]!==B[r] && evalPoly(P,p*q,A[l]*B[r])===0n));
      const count = E.flat().filter(Boolean).length;
      for (let l = 0; l < M; l++) for (let s = l+1; s < M; s++) {
        ok(E[l].filter((b,r) => b&&E[s][r]).length <= d*d,"left codegree");
        ok(E.filter(row => row[l]&&row[s]).length <= d*d,"right codegree");
      }
      ok(count*count-M*count <= d*d*M*M*(M-1), "quadratic edge bound");
      graphEdges += count; graphs++;
    }
  }
}
ok(graphEdges > 100, "nonempty tested incidences");

// Rank-one arithmetic classification, tested independently of local maps.
for (let a=-3; a<=3; a++) for (let b=1; b<=3; b++) {
  if (a===0 || gcd(BigInt(a),BigInt(b))!==1n) continue;
  const pa=BigInt(Math.max(a,0)), na=BigInt(Math.max(-a,0)), pb=BigInt(b);
  for (let i=0; i<products.length; i++) for (let j=0; j<products.length; j+=5) {
    const n0=products[i].x, y0=products[j].x;
    let cnum=y0**pb*n0**na, cden=n0**pa;
    const g=gcd(cnum,cden); cnum/=g; cden/=g;
    const hit=[];
    for (const {x:n} of products) {
      const matching=products.filter(({x:y}) => cden*y**pb*n**na===cnum*n**pa);
      if (matching.length) hit.push({n, y: matching[0].x});
    }
    if (b!==1 || Math.abs(a)!==1) ok(hit.length<=1,"valuation collapse");
    else if (a===-1) ok(hit.length<=6,"reciprocal ceiling");
    else if (cden===1n) ok(hit.every(({n,y})=>n===y),"integer multiplier");
    else ok(hit.length<=M-1 && hit.every(({n})=>n%cden===0n),"denominator star");
    curves++;
  }
}
const h=primes[0]*primes[1]*primes[2]*primes[3];
ok(products.filter(({x})=>products.some(({x:y})=>x*y===h)).length===6,
   "six unordered positives on reciprocal curve");

// The one-local check deliberately allows every possible second factor.
for (let k = 0; k < 25; k++) {
  const A = perm(k,[1,3,7,9][k%4]), u = BigInt(k+1);
  for (let i = 0; i < M; i++) {
    const j=(i+1+k)%M, a=A[i], b=primes[(i+5+k)%M];
    const x=primes[i]*primes[j], y=a*b, t=BigInt(1+k%3);
    const pool = [
      [[0,1,1n],[1,0,u],[0,0,-y-u*x]],
      [[0,1,1n],[Number(t),0,a],[0,0,-y-a*x**t]],
      [[0,1,1n],[0,0,-y]],
      [[0,1,1n],[2,0,1n],[1,0,1n],[0,0,-y-x*x-x]]
    ];
    for (const P of pool) {
      const G = P.filter(([,j]) => j===0);
      const c = G.reduce((g,[,,coeff])=>gcd(g,coeff),0n);
      const d = degree(G);
      let covered=0;
      for (let l=0; l<M; l++) {
        const p=primes[l], a=A[l];
        const E=primes.filter(q=> q!==p && products.some(({a:b,b:c0,x:y}) =>
          (a===b||a===c0) && gcd(p*q,y)===1n && gcd(c,y)===1n &&
          evalPoly(P,p*q,y)===0n));
        ok(E.length<=d,"fresh root count per left prime");
        for (const q of E) ok(evalPoly(G,p*q,0n)%a===0n,"slice reduction");
        covered+=E.length;
      }
      ok(covered<=M*d,"aggregate slice bound");
      slices++;
    }
  }
}
for (const {a,b,x} of products) {
  ok(products.filter(({x:y})=>gcd(x,y)>1n).length===2*M-3,"uniform overlap count");
  // Draw the random constant chart by drawing its index once. Its conditional
  // output multiset at every input is exactly the same uniform output pool.
  for (const {a:c,b:d,x:y} of products) {
    ok(evalPoly([[0,1,1n],[0,0,-y]],x,c*d)===0n && y%c===0n,
       "constant query, coefficient exception");
  }
}
console.log("OK: "+checks+" exact checks; "+graphs+" rank-two graphs with "+
            graphEdges+" incidences, "+curves+" rank-one tests, "+slices+" slices.");
