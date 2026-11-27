'use strict';
const assert=require('node:assert/strict'); let exact=0,numeric=0;
function c(b,m){assert(b,m);exact++;}
function near(a,b,t=1e-9){assert(Number.isFinite(a)&&Math.abs(a-b)<=t,[a,b,t].join(' '));numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
for(let places=1;places<=9;places++)for(let mask=0;mask<(1<<places);mask++){
  const d=seq(places).map(i=>1+((mask>>i)&1)),n=d.reduce((a,b)=>a+b,0);
  for(let i=0;i<places;i++){
    const num=d.map((_,j)=>n*Number(i===j)-d[i]);
    c(num.reduce((u,v,j)=>u+v*d[j],0)===0);
    const w=d.map((_,j)=>17-3*j);
    const meanNum=d.reduce((u,v,j)=>u+v*w[j],0);
    const initialShape=w.map(wj=>n*wj-meanNum);
    const rel=initialShape.map((v,j)=>v+3*num[j]);
    c(rel.reduce((s,v,j)=>s+d[j]*v,0)===0);
    for(let j=0;j<places;j++)c(rel[j]+meanNum+3*d[i]===n*(w[j]+3*Number(i===j)));
    if(places===3){
      const [j,k]=seq(3).filter(x=>x!==i);
      c(num[j]===num[k]&&num[i]-num[j]===n);
    }
  }
}
const mod=(a,p)=>(a%p+p)%p;
function rank(M,p) {
  const B=M.map(r=>r.map(v=>mod(v,p)));let r=0;
  for(let j=0;j<B[0].length&&r<B.length;j++){
    const pvt=B.findIndex((row,i)=>i>=r&&row[j]!==0);
    if(pvt<0)continue;
    [B[r],B[pvt]]=[B[pvt],B[r]];
    for(let i=r+1;i<B.length;i++)if(B[i][j]!==0){
      const u=B[i][j],v=B[r][j];
      for(let h=j;h<B[0].length;h++)B[i][h]=mod(v*B[i][h]-u*B[r][h],p);
    }
    r++;
  }
  return r;
}
let rng=0x34b53021;
function next(n){rng=(Math.imul(rng,1664525)+1013904223)>>>0;return rng%n;}
for(const p of [3,5,7,11,13,17,19,23]){
 for(let tr=0;tr<40;tr++){
   const w=seq(p).map(()=>next(19)-9);
   w[0]-=w.reduce((a,b)=>a+b,0);
   if(!w.some(x=>x!==0))continue;
   const M=seq(p).map(i=>seq(p).map(j=>w[mod(j-i,p)]));
   c(M.every(r=>r.reduce((a,b)=>a+b,0)===0));
   c([1009,1013,1019,1021,1031].some(l=>rank(M,l)===p-1));
 }
}
function mul(a,b,f){
 const n=f.length,p=Array(2*n-1).fill(0n);
 for(let i=0;i<n;i++)for(let j=0;j<n;j++)p[i+j]+=a[i]*b[j];
 for(let k=2*n-2;k>=n;k--)for(let j=0;j<n;j++)p[k-n+j]-=p[k]*f[j];
 return p.slice(0,n);
}
let one=(n)=>[1n,...Array(n-1).fill(0n)];
let eq=(a,b)=>a.every((u,i)=>u===b[i]);
const quartic=[-2n,0n,0n,0n];
const gamma=[1n,0n,1n,0n],gammaInv=[-1n,0n,1n,0n];
c(eq(mul(gamma,gammaInv,quartic),one(4)));
const cubic=[-1n,-3n,0n];
c(eq(mul([0n,1n,0n],[-3n,0n,1n],cubic),one(3)));
c(eq(mul([1n,1n,0n],[2n,1n,-1n],cubic),one(3)));
// The complex place in the quartic sees the reciprocal modulus.
const alpha=Math.sqrt(2), logs=[Math.log1p(alpha),Math.log1p(alpha),Math.log(Math.abs(1-alpha))];
near(logs[2],-logs[0]);near(logs[0]+logs[1]+2*logs[2],0);
const direction=[-0.5,-0.5,0.5];const period=2*logs[0];
for(let i=0;i<3;i++)near(logs[i]+period*direction[i],0);
function simpson(f,T,N=8192){
 let a=T/N,s=f(0)+f(T);
 for(let j=1;j<N;j++)s+=(j%2?4:2)*f(a*j);
 return a*s/3;
}
for(const vel of [[1,Math.sqrt(2)],[1,Math.sqrt(3)],[Math.log(2),Math.log(3)]]){
 for(let x=-4;x<=4;x++)for(let y=-4;y<=4;y++){
   if(!x&&!y)continue;
   const f=2*Math.PI*(x*vel[0]+y*vel[1]),v=(x+2*y)*0.17;
   for(const T of [0.12,0.6,1.4,2.7]){
     const truth=(Math.sin(f*T+v)-Math.sin(v))/(f*T);
     near(simpson(t=>Math.cos(f*t+v),T)/T,truth,8e-9);
     c(Math.abs(truth)<=Math.min(1,2/(Math.abs(f)*T))+1e-14);
   }
 }
}
console.log('PASS: '+exact+' exact/structural and '+numeric+' numerical checks');
