"use strict";

// Fixed toy wheels. This audits conditional residues and moment identities,
// not the analytic tail estimates and not the factorization of any input.
const assert = (b,msg) => { if (!b) throw new Error(msg); };
const primes = [5,7,11,13];
const Qsmall = 6;
const Qmodel = 5005;
const bit = (mask,i) => !!(mask & (1<<i));
const mod = (n,p) => ((n%p)+p)%p;
let checks = 0;
function check(b,msg){ assert(b,msg); ++checks; }
function choose(n,k){ let out=1n; for(let j=1;j<=k;j++) out=out*BigInt(n-j+1)/BigInt(j); return out; }

for(const H of [4,7,11,16]) for(let a=0;a<Qsmall;a++){
  const sites = Array.from({length:H}, (_,i)=>i+1)
    .filter(k=>mod(a+k,2)!==0 && mod(a+k,3)!==0);
  const m=sites.length;
  const M=1<<m;
  let start=29+a, size=Qmodel+45+H+a;
  const possible=Array.from({length:M},(_,mask)=>sites.filter((_,i)=>bit(mask,i)));
  const residues=possible.map(S=>primes.map(p=>new Set(S.map(k=>mod(-k,p)))));
  function surviving(n){
    let N=0;
    for(const k of sites) if(primes.every(p=>mod(n+k,p)!==0)) N++;
    return N;
  }
  function fullJoint(mask){
    return residues[mask].reduce((n,A,i)=>n*(primes[i]-A.size),1);
  }
  for(let mask=0;mask<M;mask++){
    const A=residues[mask];
    let direct=0, short=0;
    const intersections=Array(1<<primes.length).fill(0);
    for(let t=0;t<Qmodel;t++) {
      const n=a+Qsmall*t;
      if(primes.every((p,i)=>!A[i].has(mod(n,p)))) direct++;
    }
    for(let t=start;t<start+size;t++){
      const n=a+Qsmall*t;
      const hit=primes.reduce((e,p,i)=>A[i].has(mod(n,p))?e|(1<<i):e,0);
      if(!hit) short++;
      for(let e=0;e<intersections.length;e++) if((hit&e)===e) ++intersections[e];
    }
    check(direct===fullJoint(mask),"independent product != complete CRT period");
    const byOrder=Array(primes.length+1).fill(0);
    for(let e=0;e<intersections.length;e++){
      const rows=primes.filter((p,i)=>bit(e,i));
      const den=rows.reduce((d,p)=>d*p,1);
      const num=A.reduce((x,S,i)=>bit(e,i)?x*S.size:x,1);
      check(Math.abs(intersections[e]*den-size*num)<=num*den,"conditional CRT intersection error");
      byOrder[rows.length]+=intersections[e];
    }
    let partial=0;
    for(let j=0;j<byOrder.length;j++){
      partial+=(j%2?-1:1)*byOrder[j];
      check(j%2 ? partial<=short : partial>=short,"Bonferroni sign");
    }
    check(short===partial,"full inclusion-exclusion");
  }
  for(let j=0;j<=6;j++){
    const direct=Array.from({length:Qmodel}, (_,t)=>BigInt(surviving(a+Qsmall*t))**BigInt(j))
       .reduce((s,x)=>s+x,0n);
    let fromTuples=0n;
    function rec(k, mask) {
      if(k===0){ fromTuples+=BigInt(fullJoint(mask)); return; }
      for(let i=0;i<m;i++) rec(k-1,mask|(1<<i));
    }
    rec(j,0);
    check(direct===fromTuples,"raw moments from ordered tuples");
    const factDirect=Array.from({length:Qmodel},(_,t)=>{
      const n=surviving(a+Qsmall*t); return n<j?0n:choose(n,j);
    }).reduce((s,x)=>s+x,0n);
    const factTheory=possible.reduce((s,S,mask)=>S.length===j?s+BigInt(fullJoint(mask)):s,0n);
    check(factTheory===factDirect,"subsets versus factorial moment");
  }
  let states=new Set([M-1]);
  for(const p of primes){
    const newStates=new Set();
    for(const mask of states){
      const N=possible[mask].length;
      let sum=0, sum2=0;
      for(let b=0;b<p;b++){
        let out=mask, K=0;
        for(let i=0;i<m;i++) if(bit(mask,i)&&mod(sites[i],p)===b){
          ++K; out &= ~(1<<i);
        }
        check(K<=Math.ceil(H/p),"one residue occupancy");
        sum+=K;
        sum2+=K*K;
        newStates.add(out);
      }
      check(sum===N,"conditional expectation of deleted sites");
      check(sum2<=Math.ceil(H/p)*N,"conditional variance envelope");
    }
    states=newStates;
  }
}
console.log(JSON.stringify({cases:24,checks}));
