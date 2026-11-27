'use strict';
const assert=require('node:assert/strict');let exact=0,numeric=0;
function ck(x,m){assert(x,m);exact++;}
function near(x,y,e=1e-9){assert(Number.isFinite(x)&&Math.abs(x-y)<=e,[x,y,e].join(' '));numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const mod=(a,p)=>(a%p+p)%p;
function quad(p){
 const v=Array(p).fill(-1);v[0]=0;
 for(let x=1;x<p;x++)v[x*x%p]=1;
 return v;
}
for(const d of [3,5,7,11,13]) {
 const q=quad(d),counts=Array(d+1).fill(0),acc=Array(d+1).fill(0);
 for(let mask=1;mask<1<<d;mask++){
  const S=seq(d).filter(i=>(mask>>i)&1),k=S.length;
  const sq=seq(d).reduce((u,i)=>u+S.reduce((z,j)=>z+q[mod(i-j,d)],0)**2,0);
  ck(sq===k*(d-k));
  counts[k]++;
  acc[k]+=sq;
 }
 for(let k=1;k<=d;k++)ck(acc[k]===counts[k]*k*(d-k));
 for(let a=1;a<d;a++)ck(q.reduce((u,v,i)=>u+v*q[(i+a)%d],0)===-1);
 // Check the without-replacement identity for a nonflat arbitrary
 // mean-zero integer vector using the same exact finite subsets.
 const f=seq(d).map(j=>j*j-7*j+1),mu=f.reduce((u,v)=>u+v,0);
 for(let i=0;i<d;i++)f[i]=d*f[i]-mu;
 const V=f.reduce((u,v)=>u+v*v,0),accF=Array(d+1).fill(0);
 for(let mask=1;mask<1<<d;mask++){
  const S=seq(d).filter(i=>(mask>>i)&1),k=S.length;
  const sq=seq(d).reduce((u,i)=>u+S.reduce((z,j)=>z+f[mod(i-j,d)],0)**2,0);
  accF[k]+=sq;
 }
 for(let k=1;k<=d;k++)ck(accF[k]*(d-1)===counts[k]*k*(d-k)*V);
}
for(const p of [3,7,11,19,23,31,43,47,59,67,71,79,83,103]) {
 const q=quad(p),S=seq(p).filter(x=>q[x]===1),count=Array(p).fill(0);
 for(const a of S)for(const b of S)count[mod(a-b,p)]++;
 ck(count[0]===(p-1)/2);
 ck(count.slice(1).every(v=>v===(p-3)/4));
}
function signs(n){
 let P=[1],Q=[1];
 while(P.length<n){[P,Q]=[P.concat(Q),P.concat(Q.map(x=>-x))];}
 return P;
}
function rootVec(d,cs,x){
 const l=d/2,R=Array(l).fill(0);
 for(let j=1;j<d;j++){
  const k=j*x%d;
  if(k<l)R[k]+=cs[j];else R[k-l]-=cs[j];
 }
 return R;
}
function mul(A,B){
 const l=A.length,R=Array(l).fill(0);
 for(let i=0;i<l;i++)for(let j=0;j<l;j++){
  if(i+j<l)R[i+j]+=A[i]*B[j];else R[i+j-l]-=A[i]*B[j];
 }
 return R;
}
for(const d of [2,4,8,16,32,64,128,256,512]) {
 const L=d/2,b=signs(L),cs=seq(d).map(j=>j===0?0:j===L?1:b[Math.min(j,d-j)]);
 const F=seq(d).map(x=>rootVec(d,cs,x));
 for(const r of F){
  let v=0,im=0;
  for(let i=0;i<L;i++){
   v+=r[i]*Math.cos(2*Math.PI*i/d);
   im+=r[i]*Math.sin(2*Math.PI*i/d);
  }
  near(im,0,1e-9);assert(Math.abs(v)/Math.sqrt(d-1)<=4+1e-9);numeric++;
 }
 if(d<=64)for(let s=0;s<d;s++){
  const total=Array(L).fill(0);
  for(let x=0;x<d;x++){
   const v=mul(F[x],F[(x+s)%d]);
   for(let j=0;j<L;j++)total[j]+=v[j];
  }
  ck(total[0]===(s===0?d*(d-1):-d));
  ck(total.slice(1).every(x=>x===0));
 }
 if(d>=4)ck((L*(L-1))%(d-1)!==0);
}
console.log('PASS: '+exact+' exact and '+numeric+' numerical checks');
