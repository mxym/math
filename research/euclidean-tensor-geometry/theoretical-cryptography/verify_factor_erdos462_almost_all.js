"use strict";
// Exact arithmetic checks for the reduction, rectangle bookkeeping, and
// log-window identities on fixed tiny fixtures. Not a test of prime estimates.
const assert=(ok,m)=>{if(!ok)throw Error(m);};
const fixed=[11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89];
const den=fixed.reduce((a,b)=>a*BigInt(b),1n);
const weights=new Map(fixed.map(p=>[p,den/BigInt(p)]));
function rankBins(primes,lo,a,b) {
  const out=[];
  let n=BigInt(lo),d=1n,j=-1;
  for(const p of primes){
    if(j===-1){n*=BigInt(a);d*=BigInt(b);j=0;}
    while(BigInt(p)*d>n){n*=BigInt(a);d*=BigInt(b);j++;}
    out.push(j);
  }
  return out;
}
let rectangles=0, windows=0, diagonal=0, mesh=0, smallThreshold=0, overlaps=0, coefficients=0;
for(const [a,b] of [[2,1],[4,3],[9,8],[17,16],[31,30]]) {
  const g=rankBins(fixed,10,a,b);
  const pairs=[];
  for(let i=0;i<fixed.length;i++)for(let j=0;j<fixed.length;j++) {
    const p=fixed[i],q=fixed[j], n=p*q;
    assert(g[i]===g[j] || (g[i]<g[j])===(p<q),"ordered disjoint bins");
    rectangles++;
    if(g[i]===g[j]) {
      assert(b*n<=a*p*p && b*p*p<=a*n,"same-bin strip in product coordinates");
      diagonal++;
    }
    pairs.push({i,j,p,q,n,w:weights.get(q),k:g[i],l:g[j]});
  }
  for(let x=100;x<=7800;x+=37)for(const h of [2,7,20,41,87]) {
    let exact=0n, lower=0n, sameBound=0n, upperDirect=0n;
    for(const t of pairs)if(x<t.n && t.n<=x+h) {
      if(t.p<=t.q)exact+=t.w;
      if(t.k<t.l)lower+=t.w;
      if(t.k===t.l)sameBound+=t.w;
      if(t.k<=t.l)upperDirect+=t.w;
    }
    assert(lower<=exact&&exact<=lower+sameBound,"rectangle bracket");
    assert(upperDirect===lower+sameBound,"full rectangle count");
    windows+=2;
  }
}
// A model center and several actual product-window steps on a rational mesh.
for(let x=120;x<2400;x+=13)for(let h=0;h<=77;h++) {
  const S=k=>{
    let z=0n;
    for(const p of fixed)for(const q of fixed)if(p<=q&&x<p*q&&p*q<=x+k)
      z+=weights.get(q);
    return z;
  };
  const M=k=>BigInt(k)*den/700n;
  const h0=h-h%5,h1=h0+5;
  const abs=x=>x<0n?-x:x;
  const left=abs(S(h0)-M(h0)),right=abs(S(h1)-M(h1));
  assert(abs(S(h)-M(h))<=(left>right?left:right)+M(h1)-M(h0),"monotone-mesh transfer");
  mesh++;
}
// Fix a tiny domain. Precompute least-factor *weights* from its sieve; no input.
const size=450, least=Array(size+1).fill(0);
for(let p=2;p<=size;p++)if(least[p]===0)
  for(let n=p;n<=size;n+=p)if(least[n]===0)least[n]=p;
for(let x=40;x<=380;x+=4)for(let h=1;h<=45;h+=4)for(const P of [2,3,5,7,11,17]) {
  let lhs=0,rhs=0;
  for(let n=x+1;n<=x+h;n++)if(least[n]<n&&least[n]<=P)lhs+=least[n];
  for(let p=2;p<=P;p++)if(least[p]===p)rhs+=h+p;
  assert(lhs<=rhs,"pointwise least-prime truncation");
  smallThreshold++;
}
// Exact Plancherel-side overlap identity: integers are formal logarithmic
// positions. Products become sums; left endpoints differ on a null set.
for(let shift=-4;shift<=4;shift++)for(let width=1;width<=17;width++) {
  const left=[[1,2],[3,-1],[5,6],[8,-3],[11,1]];
  const right=[[-7,1],[-3,-7],[4,2],[9,5],[12,-2]];
  const points=[];
  for(const [i,a] of left)for(const [j,b] of right)points.push([i+j+shift,a*b]);
  let L=0,R=0;
  for(let x=-30;x<=40;x++) {
    let f=0;
    for(const [v,w] of points)if(x<v&&v<=x+width)f+=w;
    L+=f*f;
  }
  for(const [p,a] of points)for(const [q,b] of points)R+=a*b*Math.max(0,width-Math.abs(p-q));
  assert(L===R,"short-window log overlaps");
  overlaps++;
}
const factorial=n=>{let r=1n;for(let j=2;j<=n;j++)r*=BigInt(j);return r;};
for(let j=0;j<=42;j++){
  const a=4n**BigInt(j)*factorial(2*j);
  if(j===1)assert(a===8n,"first deterministic bias");
  if(j>0) {
    const b=4n**BigInt(j-1)*factorial(2*j-2);
    assert(a===4n*BigInt(2*j)*BigInt(2*j-1)*b,"center coefficient recurrence");
  }
  coefficients++;
}
console.log({rectangles,windows,diagonal,mesh,smallThreshold,overlaps,coefficients,
             total:rectangles+windows+diagonal+mesh+smallThreshold+overlaps+coefficients});
