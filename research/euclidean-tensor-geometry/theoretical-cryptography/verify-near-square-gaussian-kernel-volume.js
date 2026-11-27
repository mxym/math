'use strict';
const assert=require('node:assert/strict');
let exact=0,numeric=0;
function ck(x,m){assert(x,m);exact++;}
function near(x,y,t=1e-9){assert(Number.isFinite(x)&&Math.abs(x-y)<=t*Math.max(1,Math.abs(y)),[x,y,t].join(' '));numeric++;}
const z0=[0n,0n],z1=[1n,0n];
const plus=(x,y)=>[x[0]+y[0],x[1]+y[1]];
const times=(x,y)=>[x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]];
const con=x=>[x[0],-x[1]];
const neg=x=>[-x[0],-x[1]];
const pair=(a,b)=>[BigInt(a),BigInt(b)];
const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
const abs2=a=>a[0]**2n+a[1]**2n;
const seq=n=>Array.from({length:n},(_,i)=>i);
const dot=(x,y)=>x.reduce((a,v,i)=>plus(a,times(v,y[i])),z0);
function det(A){
 if(A.length===0)return z1;
 let d=z0;
 for(let k=0;k<A.length;k++){
  if(eq(A[0][k],z0))continue;
  const v=times(A[0][k],det(A.slice(1).map(r=>r.filter((_,j)=>j!==k))));
  d=plus(d,k%2?neg(v):v);
 }
 return d;
}
let state=0x8294bad1;
function get(p){state=(Math.imul(state,1664525)+1013904223)>>>0;return state%p;}
function check(X){
 const r=X.length;
 const W=seq(r+1).map(j=>{
  const v=det(X.map(row=>row.filter((_,i)=>i!==j)));
  return j%2?neg(v):v;
 });
 const G=X.map(a=>X.map(b=>dot(a,b.map(con))));
 const test=pair(W.reduce((a,v)=>a+abs2(v),0n),0);
 ck(eq(det(G),test));
 ck(X.every(row=>eq(dot(row,W),z0)));
 return W;
}
for(let r=1;r<=5;r++)for(let j=0;j<63;j++){
 const X=seq(r).map(()=>seq(r+1).map(()=>pair(get(13)-6,get(17)-8)));
 check(X);
 const Y=seq(r).map(i=>seq(r+1).map(j=>j===r?pair(get(19)-9,get(19)-9):pair(Number(i===j),0)));
 const W=check(Y);
 ck(abs2(W[r])===1n);
 for(let q=0;q<21;q++){
  const a=pair(get(53)-26,get(41)-20),b=W.map(v=>times(v,a));
  ck(Y.every(row=>eq(dot(row,b),z0)));
  ck(eq(times(con(W[r]),b[r]),a));
 }
}
function simpson(fun,lo,hi,N=16384){
 const h=(hi-lo)/N;let s=fun(lo)+fun(hi);
 for(let i=1;i<N;i++)s+=(i%2?4:2)*fun(lo+i*h);
 return s*h/3;
}
const Euler=0.5772156649015328606;
let fact=1,H=0,H2=0;
for(let j=1;j<=28;j++){
 const f=x=>Math.exp(j*x-Math.exp(x))/fact;
 const lo=-42,hi=Math.log(140+5*j);
 const a=simpson(x=>x*f(x),lo,hi);
 const v=simpson(x=>x*x*f(x),lo,hi)-a*a;
 near(a,H-Euler,2e-12);near(v,Math.PI**2/6-H2,2e-12);
 fact*=j;H+=1/j;H2+=1/(j*j);
}
const rho=t=>seq(121).reduce((a,i)=>a+Math.exp(-Math.PI*(i-60)**2/(t*t)),0);
for(const t of [1,1.25,2,2.7,5.1,10]) for(const lambda of [-0.49,-0.28,0.004,0.2,0.42]){
 near(rho(t),t*rho(1/t),2e-13);
 const direct=seq(121).reduce((a,i)=>a+Math.exp(-Math.PI*(1-lambda)*(i-60)**2/(t*t)),0)/rho(t);
 const poisson=(1-lambda)**(-0.5)*rho(Math.sqrt(1-lambda)/t)/rho(1/t);
 near(direct,poisson,2e-13);
}
console.log('PASS: '+exact+' exact and '+numeric+' numerical checks');
