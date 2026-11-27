'use strict';
const assert = require('node:assert/strict');
let exact=0,numeric=0;
function check(x,msg){assert(x,msg);exact++;}
function near(x,y,e=1e-9){assert(Number.isFinite(x)&&Math.abs(x-y)<=e*Math.max(1,Math.abs(y)), [x,y,e].join(' '));numeric++;}
const range=n=>Array.from({length:n},(_,i)=>i);
const dot=(x,y)=>x.reduce((r,u,i)=>r+u*y[i],0n);
const add=(x,y)=>range(Math.max(x.length,y.length)).map(i=>(x[i]??0n)+(y[i]??0n));
const sc=(x,u)=>x.map(v=>v*u);
const mp=(x,y)=>x.reduce((r,u,i)=>add(r,[...range(i).map(()=>0n),...sc(y,u)]),[]);
const eq=(x,y)=>x.length===y.length&&x.every((u,i)=>u===y[i]);
const delta=(a,b)=>BigInt(a===b);
for(let n=1n;n<=190n;n++){
  const mom=[1n];
  for(let j=0n;j<12n;j++)mom.push((n+2n*j)*mom[mom.length-1]);
  const E=p=>dot(p,mom);
  const u=[-n,1n], h=[n*(n+2n),-2n*(n+2n),1n];
  check(E(u)===0n&&E(h)===0n&&E(mp(u,h))===0n);
  check(E(mp(u,u))===2n*n);
  check(E(mp(h,h))===8n*n*(n+2n));
  for(let b=1n;b<=9n;b++)for(let a=-b+1n;a<=2n*b;a++){
    const p=b+a,p2=p*p,b2=b*b;
    const raw=[b2*h[0],p*b*h[1],p2*h[2]];
    const c=n*(n+2n)*a*a;
    const rhs=add(add(sc(h,p2),sc(u,2n*(n+2n)*a*p)),[c]);
    check(eq(raw,rhs));
    check(E(raw)===c);
  }
}
// Both prior laws have scaled mean 1. The factor 32 in the
// denominator of (1) accounts for the doubled real complex blocks.
for(let m=1n;m<=600n;m++) {
  const real=1n*m*(m+2n), complex=(2n*m)*(2n*m+2n);
  check(complex===4n*m*(m+1n));
  for(const [s1,s2] of [[1n,0n],[0n,1n],[2n,3n],[8n,2n],[4n,17n]]) {
    check(4n*s1*real+s2*complex===4n*(s1*m*(m+2n)+s2*m*(m+1n)));
  }
}
function tensor3(a,b,c,d){
 return delta(a,b)*delta(c,d)+delta(a,c)*delta(b,d)+delta(a,d)*delta(b,c);
}
for(let n=1;n<=10;n++){
 const ix=range(n);let total=0n;
 for(const a of ix)for(const b of ix)for(const c of ix)for(const d of ix){
  const x=tensor3(a,b,c,d);total+=x*x;
 }
 check(total===3n*BigInt(n*(n+2)));
 for(const a of ix)for(const e of ix){
  let z=0n;
  for(const b of ix)for(const c of ix)for(const d of ix)z+=tensor3(a,b,c,d)*tensor3(e,b,c,d);
  check(z===3n*BigInt(n+2)*delta(a,e));
 }
 for(let seed=0;seed<15;seed++){
  const B=ix.map(i=>ix.map(j=>BigInt((i*j+(i+j)*seed+1)%13-6)));
  const trB=ix.reduce((r,i)=>r+B[i][i],0n);
  for(const c of ix)for(const d of ix){
   let z=0n;
   for(const a of ix)for(const b of ix)z+=B[a][b]*tensor3(a,b,c,d);
   check(z===trB*delta(c,d)+2n*B[c][d]);
  }
  const mean=ix.map(i=>BigInt((i*seed+i+4)%7-3));
  const S=B.map((u,i)=>B.map((v,j)=>dot(u,v)+delta(i,j)));
  const E=S.map((u,i)=>u.map((v,j)=>v-delta(i,j)));
  const trS=ix.reduce((r,i)=>r+S[i][i],0n), trE=trS-BigInt(n);
  const trS2=S.reduce((r,v)=>r+dot(v,v),0n), trE2=E.reduce((r,v)=>r+dot(v,v),0n);
  const muS=dot(mean,S.map(v=>dot(v,mean))), muE=dot(mean,E.map(v=>dot(v,mean)));
  const sq=dot(mean,mean);
  const direct=(trS+sq)**2n+2n*trS2+4n*muS-2n*BigInt(n+2)*(trS+sq)+BigInt(n*(n+2));
  check(direct===(trE+sq)**2n+2n*trE2+4n*muE);
 }
}
function gammaHalf(k){
 let z=k%2?Math.sqrt(Math.PI):1,n=k%2?0.5:1;
 while(n<k/2){z*=n;n++;}
 return z;
}
function simpson(f,hi,N=4096){
 const h=hi/N;
 let z=f(0)+f(hi);
 for(let i=1;i<N;i++)z+=f(i*h)*(i%2?4:2);
 return z*h/3;
}
for(let k=1;k<=28;k++)for(const s of [-0.19,0,0.1,0.39,0.77])for(const t of [-0.29,0,0.17,0.51]){
 const r=k/2,g=gammaHalf(k);
 const c=1/(1+s)+1/(1+t)-1;
 const value=simpson(x=>2*x**(k-1)*Math.exp(-c*x*x)/
    (g*((1+s)*(1+t))**r), Math.sqrt((k+90)/c));
 near(value,(1-s*t)**(-r),2e-11);
}
// Small bounded toy mixing distributions; use compensated low-order
// subtraction to check the uniform cubic remainder numerically.
for(let k=1;k<=240;k++)for(const ep of [0.0004,0.0013,0.004]) {
 const r=k/2,K=r*(r+1)/2;
 const vals=[-0.9,-0.2,1.1], probs=[1/3,1/3,1/3];
 const v=dot(vals.map(v=>BigInt(Math.round(v*10))**2n),[1n,1n,1n]);
 const variance=Number(v)/300;
 let chi2=0;
 for(let i=0;i<3;i++)for(let j=0;j<3;j++){
  const z=ep*ep*vals[i]*vals[j];
  chi2+=probs[i]*probs[j]*(Math.expm1(-r*Math.log1p(-z))-r*z);
 }
 const main=K*ep**4*variance**2;
 assert(Math.abs(chi2/main-1)<4*(r+2)*ep*ep+1e-7,[k,ep,chi2/main].join(' '));numeric++;
}
console.log('PASS: '+exact+' exact and '+numeric+' numerical checks');
