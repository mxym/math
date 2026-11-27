"use strict";
// Fixed toy Pascal coefficients and exact multiplicative forms of the width lemma.
let checks=0;
function check(b,msg){ if(!b) throw new Error(msg); ++checks; }
const upper=3600;
const spf=Array(upper+1).fill(0);
for(let p=2;p<=upper;++p) if(!spf[p]) for(let n=p;n<=upper;n+=p) if(!spf[n]) spf[n]=p;
const factor=n=>{
  const f=new Map();
  while(n>1){const p=spf[n];f.set(p,(f.get(p)||0)+1);n/=p;}
  return f;
};
const fac=Array.from({length:upper+1},(_,n)=>factor(n));
function vf(n,p){let out=0;while(n){n=Math.floor(n/p);out+=n;}return out;}
function bin(n,k) {let out=1n;for(let j=1;j<=k;j++)out=out*BigInt(n-j+1)/BigInt(j);return out;}
const prod=(a)=>a.reduce((x,y)=>x*BigInt(y),1n);
const abs=x=>x<0n?-x:x;
const primes=spf.flatMap((a,p)=>p>=2&&a===p?[p]:[]);
function add(target,source,sign=1){
  for(const [p,e] of source)target.set(p,(target.get(p)||0)+sign*e);
}
const solutions=[];let narrow=0;
for(let k=2;k<=9;k++){
  const denom=new Map();
  for(let i=2;i<=k;i++)add(denom,fac[i]);
  const K=prod(Array.from({length:k},(_,i)=>i+1))*prod(primes.filter(p=>p<=k));
  for(let n=2*k;n<=upper;n++){
    const top=new Map();
    for(let i=0;i<k;i++)add(top,fac[n-i]);
    const f=new Map(top);
    add(f,denom,-1);
    check([...f].every(([p,e])=>e===vf(n,p)-vf(n-k,p)-vf(k,p)),"Legendre cross-check");
    if([...f.values()].some(e=>e>1))continue;
    check([...f.values()].every(e=>e===0||e===1),"valuation range");
    const support=[...f].filter(([,e])=>e===1).map(([p])=>p).sort((a,b)=>a-b);
    const Q=support[0], P=support.at(-1);
    const C=bin(n,k);
    check(C===prod(support),"literal product");
    let mask=1n;
    for(let i=0;i<k;i++){
      const N=BigInt(n-i);
      const s=[...fac[n-i]].filter(([p])=>p<=k)
          .reduce((z,[p,e])=>z*BigInt(p)**BigInt(e),1n);
      const r=[...fac[n-i]].filter(([p])=>p>k).reduce((z,[,e])=>z+e,0);
      check(K%s===0n && N%s===0n,"small-prime bound");
      if(r){
        const b=BigInt(r);
        check(s*BigInt(Math.max(k+1,Q))**b<=N && N<=s*BigInt(P)**b,
              "exact prime-band bracket");
      } else check(s===N,"empty large-prime part");
      if(i===0)mask=s;
      if(i===1)check(mask%2n!==s%2n,"adjacent parities");
    }
    // Exact rational form of the key width inequality, tested on all qualifying
    // squarefree toy coefficients, not only those with consecutive support.
    if(Q>P/2 && Q>k && BigInt(P)>K){
      const r=[...fac[n],...fac[n-1]].filter(([p])=>p>k).reduce((z,[,e])=>z+e,0);
      check(BigInt(n)*K*BigInt(P)**BigInt(r)>=BigInt(n-1)*(K+1n)*BigInt(Q)**BigInt(r),
            "multiplicative separation");
      ++narrow;
    }
    const consecutive=primes.filter(p=>Q<=p&&p<=P);
    if(consecutive.length===support.length){
      check(prod(consecutive)===C,"endpoint pair certificate");
      solutions.push([n,k]);
    }
  }
}
solutions.sort((a,b)=>a[0]-b[0]||a[1]-b[1]);
check(JSON.stringify(solutions)===JSON.stringify([[4,2],[6,2],[7,3],[10,4],[14,4],
   [15,2],[15,6],[21,2],[715,2]]),"previously known toy solutions");
check(narrow>0,"insufficient narrow-band trials");

// Table 1 of Gafni--Tao: check the decreasing branches starting at sigma >= 4/5.
// Each entry gives A(sigma)=numerator/(a*sigma-b), and its rational left endpoint.
for(const [num,a,b,l,m] of [
  [3,2,0,4,5], [3,10,7,7,8], [24,30,11,279,314],
  [24,30,11,155,174], [3,10,7,9,10], [11,48,36,31,34],
  [391,2493,2014,14,15], [22232,163248,134765,2841,3016],
  [356,2742,2279,859,908], [3,24,20,23,24],
  [86152,1447460,1311509,2211487,2274732],
  [2,15,12,39,40], [3,40,35,41,42]
]){
  const den=BigInt(a)*BigInt(l)-BigInt(b)*BigInt(m);
  check(den>0n && 8n*BigInt(num)*BigInt(m)<=15n*den,"density table bound");
}
check(8*3<=15*(6-1),"Pintz terminal n family");
check(543*25<650*21 && 168<2*95,"exceptional exponent strict slack");
console.log(JSON.stringify({checks,narrow,knownSolutions:solutions.length}));
