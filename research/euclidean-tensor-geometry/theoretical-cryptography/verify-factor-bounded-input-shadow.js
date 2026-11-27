"use strict";
// Exact toy probability experiment. Inputs are *pairs of labels* from a short
// public prime pool, so this checker never factors a supplied integer.
const pool=[7,11,13,17,19], M=pool.length,P=pool[0],K=2;
const C2=x=>x*(x-1)/2, Acount=C2(M)-C2(M-K);
const pairs=[];for(let i=0;i<M;i++)for(let j=i+1;j<M;j++)pairs.push([i,j]);
const prod=pool.reduce((a,b)=>a*BigInt(b),1n);
let profiles=0,experiments=0,strict=0,doubleHit=0;
for(let n=2;n<=10;n++)for(let k=1;k<=n;k++){
  let best=0;
  for(let mask=0;mask<(1<<n);mask++){
    let s=0;for(let j=0;j<n;j++)s+=(mask>>j)&1;if(s>k)continue;
    let t=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)t+=Number(Boolean(mask&((1<<i)|(1<<j))));
    if(t>best)best=t;
  }
  if(best!==C2(n)-C2(n-k))throw Error("baseline");
  profiles++;
}
// First probe, one arbitrary input bit depending on the first reply, second
// probe, then output the best label for each observed transcript (Bayes 
// success). All weighted counts use a common multiple of component sizes.
for(let seed=0;seed<64;seed++){
  const s=[seed%3,(seed>>2)%3],d=[(seed>>3)%3,(seed>>1)%3];
  const scores=new Map();
  let dep=0n,shadow=0n;
  const query=(i,u,v,x,y,prior,bit)=>{
    const start=(seed+3*i+2*prior+bit)%M;
    const T=Array.from({length:s[i]},(_,j)=>(start+j)%M);
    const z=(r,z0)=>T.includes(r)||Array.from({length:d[i]},(_,j)=>(seed+prior+bit+2*i+j)%pool[r]).includes(z0);
    return Number(z(u,x)&&z(v,y));
  };
  let pairIndex=0;
  for(const [u,v] of pairs){
    const p=pool[u],q=pool[v],unit=prod/BigInt(p*q);
    const hint=r=>Number(((seed*13+pairIndex*7+pairIndex*pairIndex+(2*seed+3)*r+pairIndex*r)%17)<8);
    const frozenHint=hint(0);if(u===frozenHint||v===frozenHint)shadow+=prod;
    for(let x=0;x<p;x++)for(let y=0;y<q;y++){
      const r=query(0,u,v,x,y,0,0),h=hint(r);
      const t=query(1,u,v,x,y,r,h);
      const key=[r,h,t].join();
      if(!scores.has(key))scores.set(key,Array(M).fill(0n));
      const arr=scores.get(key);arr[u]+=unit;arr[v]+=unit;
      if(r||t)dep+=unit;
      if(r&&s[0]===2&&d[0]===0)doubleHit++;
    }
    pairIndex++;
  }
  let success=0n;for(const arr of scores.values())success+=arr.reduce((a,b)=>a>b?a:b);
  const denominator=prod*BigInt(C2(M));
  if(shadow>BigInt(Acount)*prod)throw Error("shadow guess");
  if(success>BigInt(Acount)*prod+dep)throw Error("success departure bound");
  // d²/P² + (d/P)min(1,2Ks/M) + min(1,K*C(s,2)/C(M,2)).
  const scale=BigInt(P*P*M*C2(M));
  let bound=0n;
  for(let i=0;i<2;i++){
    bound+=BigInt(d[i]*d[i])*scale/BigInt(P*P);
    bound+=BigInt(d[i]*Math.min(M,2*K*s[i]))*scale/BigInt(P*M);
    bound+=BigInt(Math.min(C2(M),K*C2(s[i])))*scale/BigInt(C2(M));
  }
  if(dep*scale>denominator*bound)throw Error("content probability");
  if(BigInt(Acount)*prod*scale+denominator*bound<denominator*scale)strict++;
  experiments++;
}
if(!strict||!doubleHit)throw Error("missing nontrivial case");
console.log({profiles,adaptiveExperiments:experiments,finiteBoundsBelowOne:strict,constantDoubleContentObservations:doubleHit});
