"use strict";
// Forward toy invariants of explicitly generated small prime pairs only.
const must=(b,m)=>{if(!b)throw Error(m);};
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a;};
const lcm=(a,b)=>a/gcd(a,b)*b;
function form(x){
 const F=[];for(let d=2;d*d<=x;d++)if(x%d===0){
  let e=0;while(x%d===0){x/=d;e++;}F.push([d,e]);
 }if(x>1)F.push([x,1]);return F;
}
const tau=F=>F.reduce((r,[,e])=>r*(e+1),1);
const phi=(m,F)=>F.reduce((r,[p])=>r/p*(p-1),m);
function divs(F){
 let D=[1];for(const [p,e] of F){
  const E=D.slice();let a=1;for(let j=1;j<=e;j++){a*=p;D.push(...E.map(d=>d*a));}
 }return D;
}
function merge(A,B){
 const t=new Map(A);for(const [p,e] of B)t.set(p,Math.max(e,t.get(p)||0));return [...t.entries()];
}
let pools=0,pairs=0,distinctFibers=0,repeatedFibers=0,meanIdentities=0,weightedChecks=0,arithmeticChecks=0;
for(let n=4;n<=11;n++){
 const P=2**(n-1),S=Array.from({length:P},(_,i)=>P+i).filter(prime),a=S.map(p=>p-1),F=a.map(form);
 const buckets=new Map(),E=[];
 for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++){
  const k=gcd(a[i],a[j]),ell=lcm(a[i],a[j]),L=merge(F[i],F[j]);
  if(!buckets.has(ell))buckets.set(ell,{L,divs:divs(L),values:[]});
  const t=buckets.get(ell);t.values.push({k,i,j});E.push(ell);pairs++;
  must(ell*k===a[i]*a[j],"product identity");
 }
 let regular=0n;for(const [ell,{L,divs:D,values}] of buckets){
  const f=values.length;
  const exponentBound=L.reduce((r,[,e])=>r*(2*e+1),1);
  must(f<=exponentBound,"prime-power exponent choices");
  if(f>1)repeatedFibers++;
  for(const {k} of values){
   for(const v of values)must(v.k<=4*k&&ell%v.k===0,"candidate gcd limitation");
   let bound=0;
   for(const d of D){if(d>4*k)continue;
    const r=ell/d,g=L.reduce((s,[p])=>s+Number(r%p===0),0);bound+=2**g;
   }
   must(f<=bound&&bound<=4*k*2**L.length,"arithmetic fiber bounds");arithmeticChecks++;
  }
  regular+=BigInt(f)**2n;
  distinctFibers++;
 }
 const biased=E.reduce((s,k)=>s+BigInt(buckets.get(k).values.length),0n);
 must(regular===biased,"size-biased collision identity");meanIdentities++;
 for(let T=1;T<=Math.floor(P**0.25);T++){
  const exact=a.reduce((s,x,i)=>s+((x%T)===0?tau(F[i]):0),0);
  let envelope=0;for(let r=1;r<=Math.floor(Math.sqrt(2*P));r++){
   const c=gcd(T,r),t=T*(r/c);
   must(t===lcm(T,r),"lcm decomposition");
   envelope+=2*a.filter(x=>x%t===0).length;
  }
  must(exact<=envelope,"weighted divisor hyperbola");weightedChecks++;
 }
 pools++;
}
for(let k=1;k<=75;k++)for(let s=1;s<=75;s++){
 const A=form(k),B=form(s),C=form(k*s);
 must(tau(C)<=tau(A)*tau(B)&&phi(k*s,C)>=phi(k,A)*phi(s,B),"local multiplicativity inequalities");
 arithmeticChecks++;
}
must(repeatedFibers>0,"nontrivial equal values");
console.log({pools,pairs,distinctFibers,repeatedFibers,meanIdentities,weightedChecks,arithmeticChecks});