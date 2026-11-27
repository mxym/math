'use strict';
const assert=require('node:assert/strict');
let exact=0,numeric=0;
function ck(x,msg){assert(x,msg);exact++;}
function near(x,y,t=2e-11){assert(Number.isFinite(x)&&Math.abs(x-y)<=t*Math.max(1,Math.abs(y)),[x,y,t].join(' '));numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const dot=(u,v)=>u.reduce((r,a,i)=>r+a*v[i],0n);
const tr=A=>A.reduce((u,r,i)=>u+r[i],0n);
const mp=(A,B)=>A.map(r=>B[0].map((_,j)=>dot(r,B.map(c=>c[j]))));
const add=(A,B)=>A.map((r,i)=>r.map((u,j)=>u+B[i][j]));
const sc=(A,t)=>A.map(r=>r.map(x=>x*t));
const ident=(n,t=1n)=>seq(n).map(i=>seq(n).map(j=>i===j?t:0n));
const sub=(A,B)=>add(A,sc(B,-1n));
const eq=(A,B)=>A.every((r,i)=>r.every((u,j)=>u===B[i][j]));
let state=0x247da083;
function pick(n){state=(Math.imul(state,1664525)+1013904223)>>>0;return state%n;}
const mat=n=>seq(n).map(()=>seq(n).map(()=>BigInt(pick(23)-11)));
const sym=n=>{const T=mat(n);return T.map((r,i)=>r.map((u,j)=>u+T[j][i]));};
const del=(a,b)=>BigInt(a===b);
const Cov=(i,j,k,l)=>del(i,k)*del(j,l)+del(i,l)*del(j,k);
const mkPair=n=>seq(n).flatMap(i=>seq(n).map(j=>[i,j]));
for(let p=1;p<=8;p++)for(let j=0;j<49;j++){
 const idx=mkPair(p),B=sym(p),D=sym(p),C=sym(p);
 const left=mp(mp(C,B),C),right=mp(mp(C,D),C);
 const deltaB=sub(left,B),deltaD=sub(right,D);
 let cov=0n,trace2=0n;
 for(const [i,j] of idx)for(const [a,b] of idx){
  cov+=deltaB[i][j]*deltaD[a][b]*Cov(i,j,a,b);
  trace2+=B[i][j]*B[a][b]*Cov(j,a,b,i);
 }
 ck(cov===2n*tr(mp(deltaB,deltaD)));
 ck(trace2===tr(mp(B,B))+tr(B)**2n);
 // Covariance of a weighted sum of independent Wisharts, multiplied
 // by the common denominator, and its mixed tensor contraction.
 const widths=[5n,11n,19n,37n].slice(0,1+pick(4));
 const den=widths.reduce((u,v)=>u*v,1n),a=widths.reduce((u,v)=>u+den/v,0n);
 const lhs=idx.reduce((r,[i,j])=>r+widths.reduce((z,d)=>z+(den/d)*Cov(i,j,i,j),0n),0n);
 ck(lhs===BigInt(p*(p+1))*a);
 const off=idx.reduce((r,[i,j])=>r+(i<j?a*Cov(i,j,i,j):0n),0n);
 ck(off===BigInt(p*(p-1)/2)*a);
 // Exact determinant-kernel matrix identity before taking determinants.
 const X=sc(B,200n),Y=sc(D,200n),S=add(ident(p,70n),X),T=add(ident(p,70n),Y);
 ck(eq(sub(ident(p,4900n),mp(X,Y)),sub(sc(add(S,T),70n),mp(S,T))));
}
// Gaussian rectangle fourth-moment combinatorics.
function rects(p,q){
 const out=[];
 for(let i=0;i<p;i++)for(let k=i+1;k<p;k++)for(let j=0;j<q;j++)for(let l=j+1;l<q;l++){
  const mask=[i*q+j,k*q+j,i*q+l,k*q+l].reduce((u,a)=>u|1n<<BigInt(a),0n);
  out.push({mask,R:1n<<BigInt(i)|1n<<BigInt(k),C:1n<<BigInt(j)|1n<<BigInt(l)});
 }
 return out;
}
function bits(a){let z=0;for(;a!==0n;a&=a-1n)z++;return z;}
for(let p=2;p<=6;p++)for(let q=2;q<=6;q++){
 const r=rects(p,q),groups=new Map();let n=0;
 for(let i=0;i<r.length;i++)for(let j=0;j<i;j++){
  const x=r[i].mask^r[j].mask,prev=groups.get(x)??[];
  for(const [a,b] of prev){
   ck(a!==i&&a!==j&&b!==i&&b!==j);
   const rows=bits(r[i].R|r[j].R|r[a].R|r[b].R),cols=bits(r[i].C|r[j].C|r[a].C|r[b].C);
   ck(rows<=4&&cols<=4&&(rows<4||cols<4));n++;
  }
  prev.push([i,j]);groups.set(x,prev);
 }
 ck(n%3===0);
}
// Heterogeneous Wishart mgf expansions: cancellation and scale checks
// using exact (finite-dimensional) diagonal Gaussian integrals.
for(const p of [2,4,8,15,25])for(const q of [p,3*p,7*p])for(const scale of [2,7,20]){
 const ds=[p*q*scale,p*q*(scale+1),p*q*(scale+7)],a=ds.reduce((r,d)=>r+1/d,0);
 const u=seq(p).map((_,i)=>(i%4-1.5)/Math.sqrt(q));
 const sq=u.reduce((r,x)=>r+x*x,0);
 const log=ds.reduce((r,d)=>r-d/2*u.reduce((z,x)=>z+(Math.log1p(-q*x/d)+q*x/d),0),0);
 const quad=q*q*a*sq/4;
 const bs=ds.reduce((r,d)=>r+1/d**2,0),max=Math.max(...u.map(Math.abs));
 assert(Math.abs(log-quad)<q**3*bs*max*sq+1e-10);numeric++;
 let series=0;
 for(let h=2;h<=13;h++){
  const w=u.reduce((r,x)=>r+x**h,0);
  series+=w*ds.reduce((r,d)=>r+(q/d)**h*d/(2*h),0);
 }
 near(log,series,2e-5);
}
console.log('PASS: '+exact+' exact and '+numeric+' numerical checks');
