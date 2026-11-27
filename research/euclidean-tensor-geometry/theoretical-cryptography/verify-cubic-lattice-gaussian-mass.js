"use strict";
// Deterministic replay on elementary generated lattices and exact theta series.
let exact = 0, numerical = 0;
function check(ok, why, isExact = true) {
  if (!ok) throw new Error(why);
  if (isExact) ++exact; else ++numerical;
}
const cap = 320, zero = () => Array(cap + 1).fill(0n);
function add(a, b, factor = 1n) { return a.map((x, i) => x + factor*b[i]); }
function mul(a, b) {
  const c = zero();
  for (let i = 0; i <= cap; ++i) if (a[i])
    for (let j = 0; i + j <= cap; ++j) if (b[j]) c[i+j] += a[i]*b[j];
  return c;
}
function fourth(a) { const b = mul(a,a); return mul(b,b); }
const th3 = zero(), th2 = zero(), th4 = zero();
for (let j = -20; j <= 20; ++j) {
  if (4*j*j <= cap) { ++th3[4*j*j]; th4[4*j*j] += j%2 ? -1n : 1n; }
  if ((2*j+1)**2 <= cap) ++th2[(2*j+1)**2];
}
const a = fourth(th3), b = fourth(th2), c = fourth(th4);
const d4twice = add(a,c), d4dual = add(a,b), twiceGap = mul(b,c);
const twiceGapAlt = add(mul(d4twice,d4dual),mul(a,a),-2n);
for (let j = 0; j <= cap; ++j) {
  check(a[j] === b[j]+c[j], "Jacobi coefficient "+j);
  check(twiceGap[j] === twiceGapAlt[j], "D4 orthogonal sum coefficient "+j);
  check(d4twice[j]%2n === 0n, "parity projector coefficient "+j);
}
check(d4twice[0]===2n && d4twice[4]===0n && d4twice[8]===48n, "D4 first shell");
check(d4dual[0]===1n && d4dual[4]===24n, "D4 dual first shell");
check(twiceGap[4]===16n, "difference in the first shell");
check(8n*101n**4n < 9n*100n**4n && 101n**2n < 2n*100n**2n,"strict-minimum rescaling certification");

function factorialDouble(k) { let a=1n; for(let j=1;j<=k;++j)a*=BigInt(2*j-1); return a; }
for (let n=2;n<=5;++n) {
  const edges=[]; for (let i=0;i<n;++i) for(let j=i+1;j<n;++j) edges.push([i,j]);
  for (let seed=0;seed<47;++seed) for(let k=2;k<=7;++k) {
    const d=Array(n).fill(0);
    let lhs=0n,rhs=0n,terms=0;
    // Enumerate multisets of k edges, tracking the multinomial count.
    const fact=[1n]; for (let i=1;i<=k;++i) fact.push(BigInt(i)*fact.at(-1));
    function visit(e,remain,weight,factor) {
      if (e===edges.length) {
        if (remain || d.some(x=>x%2)) return;
        const support=d.filter(x=>x).length;
        check(support>=2,"even monomial supported on both ends");
        check(d.reduce((a,x)=>a+x,0)===2*k,"quadratic degree");
        let g=1n; for(const degree of d)g*=factorialDouble(degree/2);
        const raw=weight*g*(fact[k]/factor);
        lhs+=raw*7n**BigInt(n-support);
        rhs+=(raw<0n?-raw:raw)*7n**BigInt(n-2);
        ++terms;
        return;
      }
      const [i,j]=edges[e], v=BigInt((3*seed+5*i+11*j+e*e)%9-4);
      for(let h=0;h<=remain;++h){
        d[i]+=h; d[j]+=h;
        visit(e+1,remain-h,weight*v**BigInt(h),factor*fact[h]);
        d[i]-=h; d[j]-=h;
      }
    }
    visit(0,k,1n,1n);
    check(lhs<=rhs && -lhs<=rhs, "sparse signed even-moment comparison");
    check(terms>0 || (n===2 && k%2===1), "expected surviving monomials");
  }
}

const { exp, expm1, log1p, PI, abs, hypot } = Math;
function th(t) {
  let z=1, u=0, v=0;
  for(let k=1;k<=20;++k){ const r=2*exp(-t*k*k); z+=r; u+=r*k*k; v+=r*k**4; }
  return [z,u/z,v/z];
}
function grams(B) {
  const n=B.length,U=B.map((row,i)=>row.concat(Array.from({length:n},(_,j)=>+(i===j))));
  for(let i=0;i<n;++i){
    const p=U[i][i]; U[i]=U[i].map(x=>x/p);
    for(let j=0;j<n;++j)if(i!==j){
      const f=U[j][i]; U[j]=U[j].map((x,k)=>x-f*U[i][k]);
    }
  }
  const V=U.map(r=>r.slice(n));
  const G=B.map((r,i)=>r.map((x,j)=>B.reduce((a,row)=>a+row[i]*row[j],0)));
  const H=V.map((r,i)=>r.map((x,j)=>r.reduce((a,y,k)=>a+y*V[j][k],0)));
  return [G,H];
}
function thetaLoss(G,t) {
  const n=G.length, z=Array(n).fill(0), E=G.map((r,i)=>r.map((x,j)=>x-+(i===j)));
  let gap=0;
  function addPoint(r) {
    let q=0;
    for(let i=0;i<n;++i)for(let j=0;j<n;++j)q+=z[i]*z[j]*E[i][j];
    gap+=exp(-t*r)*(-expm1(-t*q));
  }
  function visit(i,r) {
    if(i===n) return addPoint(r);
    for(let j=-6;j<=6;++j){ z[i]=j; visit(i+1,r+j*j); }
  }
  visit(0,0);
  return -log1p(-gap/th(t)[0]**n);
}
for (let k=0;k<128;++k){
  const t=PI*(1+3*k/127), xi=t*th(t)[1], td=PI*PI/t;
  check(abs(xi+td*th(td)[1]-.5)<2e-15,"Poisson moment symmetry",false);
  check(xi>0 && xi<=.250000000000001, "one-dimensional monotonic bound",false);
  const m=th(t)[1], m4=th(t)[2];
  check(m-t*(m4-m*m)<0,"log-scale derivative of xi",false);
}
for(const n of [2,3,4]) for(let seed=0;seed<11;++seed){
  const A=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>j<=i?0:((i*9+j*(seed+3)+seed)%9-4)/4));
  A[0][1]=1;
  for(const h of [1/64,1/512,1/4096]){
    const B=A.map((r,i)=>r.map((x,j)=>h*x+ +(i===j)));
    for(const G of grams(B)){
      const E=G.map((r,i)=>r.map((x,j)=>x- +(i===j)));
      const s=hypot(...E.flat()), d=E.map((r,i)=>r[i]), dsum=d.reduce((a,x)=>a+x,0);
      check(d.every(x=>x>=-1e-15), "axis constraints of generated shear and its dual",false);
      check(abs(dsum-s*s/2) < s**3, "determinant trace compensation",false);
      for(const t of [PI,3.4,5,9,16,40,120]){
        const loss=thetaLoss(G,t), xi=t*th(t)[1], pred=xi*(.5-xi)*s*s;
        const axis=d.reduce((a,x)=>a-expm1(-t*x),0);
        check(loss>0 && axis>0, "strict mass loss "+[n,seed,h,t,loss],false);
        check(abs(loss/pred-1)<4*(s+t*s*s), "uniform quadratic term "+[n,seed,h,t,loss,pred],false);
        if(t>=16) check(abs(loss/(2*exp(-t)*axis)-1)<4e-5, "resolved axis-shell asymptotics",false);
      }
    }
  }
}
// High rank via exact product structure, without an n-dimensional enumeration.
for (const n of [2,64,2048,65536,1048576]) for (const t of [PI,15,120]){
  const h=1/(256*Math.sqrt(n)), [G]=grams([[1,h],[0,1]]);
  const blockLoss=thetaLoss(G,t);
  const s2=n* (h*h+h**4/2), xi=t*th(t)[1];
  check(abs((n/2)*blockLoss/(xi*(.5-xi)*s2)-1)<.002,"dimension-free product check",false);
}
// A diagonal violation gives the opposite comparison in the narrow limit.
for (const h of [1/500,1/100,1/20]) {
  const g=1+h, G=[[g,0],[0,1/g]];
  for (const t of [PI,8,35,100]) check(thetaLoss(G,t)<0,"short vector counterexample",false);
}
console.log(JSON.stringify({exact,numerical}));
