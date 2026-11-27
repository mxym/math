"use strict";
// Fixed toy covering fixtures only. No input modulus or factorization task.
const upper=2200;
const spf=Array(upper+1).fill(0);
for(let p=2;p<=upper;p++)if(!spf[p])for(let t=p;t<=upper;t+=p)if(!spf[t])spf[t]=p;
const primes=spf.flatMap((p,i)=>p&&p===i?[p]:[]);
function check(b,msg){if(!b)throw Error(msg);++checks;}
function factor(n){const f=new Map;while(n>1){const p=spf[n];f.set(p,(f.get(p)||0)+1);n/=p;}return f;}
const factors=Array.from({length:upper+1},(_,n)=>factor(n));
const z=(n,S)=>[...factors[n]].filter(([p])=>!S.has(p)).reduce((t,[p,e])=>t*p**e,1);
let checks=0, cases=0, usedReserves=0, mixedMoments=0;
const examples=[];

const mod=(n,m)=>(n%m+m)%m;
function inv(n,m){
  let a=n,b=m,x=1n,y=0n;
  while(b){const q=a/b;[a,b]=[b,a-q*b];[x,y]=[y,x-q*y];}
  check(a===1n,"coprime CRT coordinate");
  return mod(x,m);
}
function vp(n,p){let s=0;while(n%p===0n){n/=p;s++;}return s;}
function vf(n,p){let s=0n;while(n){n/=p;s+=n;}return s;}
const fixtures=[
 {k:15,B:2,setup:[[5,1],[11,5]],reserve:{Q:5,p:11,j:5}},
 {k:21,B:2,setup:[[7,1],[5,2],[17,5]]},
 {k:22,B:2,setup:[[11,1],[7,5],[19,7],[13,11],[5,3]]},
 {k:33,B:2,setup:[[11,1],[23,11]],reserve:{Q:11,p:23,j:11}},
 {k:35,B:2,setup:[[7,1],[29,7],[17,13],[13,11],[11,6]]},
 {k:36,B:2,setup:[[3,1],[5,3],[11,5],[31,29],[29,9],[23,15],[13,11]]},
 {k:50,B:2,setup:[[5,1],[23,5],[41,37],[19,13],[37,19],[31,23],[13,12]]},
 {k:70,B:2,setup:[[5,1],[7,4],[11,5],[13,7],[23,19],[17,13],[19,17],[67,23],[61,43],[59,37],[53,35],[47,29]]}
];
for(const {k,B,setup,reserve} of fixtures){
  const R=new Map(setup), S=new Set(R.keys());
  const weight=(j,A)=>z(j,new Set(A.keys()))*[...A]
       .filter(([p,b])=>j%p===b).reduce((u,[p])=>u*p,1);
  const wanted=Array.from({length:k},(_,i)=>weight(i+1,R));
  check(wanted.every(g=>g>=B),"initial covering weights");
  check(S.size===setup.length,"distinct primes");
  if(reserve){
    const {Q,p,j}=reserve;
    const before=new Map([[Q,1]]);
    const beforeBad=Array.from({length:k},(_,i)=>i+1).filter(x=>weight(x,before)<B);
    check(beforeBad.length===1&&beforeBad[0]===j&&p%Q===1&&p>k/2&&k%p<j,
        "reserve repairs one slot without reopening its own");
    usedReserves++;examples.push({k,Q,p,j});
  }
  let M=1n,N=0n;
  const relevant=primes.filter(p=>p<=k);
  for(const p0 of relevant){
    const p=BigInt(p0);let P=p;
    while(P<=BigInt(k))P*=p;
    const a=R.get(p0);
    check(a===undefined||(a>k%p0&&a<p0),"class is allowed");
    const rhs=a===undefined?BigInt(k):BigInt(k)-(P-p+BigInt(a));
    N+=M*mod((rhs-N)*inv(M%P,P),P);M*=P;
    check(mod(N-rhs,P)===0n,"CRT lift");
  }
  N+=M;
  const small=Array(k).fill(1n);
  for(const p0 of relevant){
    const p=BigInt(p0),v=vf(N,p)-vf(N-BigInt(k),p)-vf(BigInt(k),p);
    check(v===0n,"independent factorial valuation after lifting");
    for(let j=1;j<=k;j++)small[j-1]*=p**BigInt(vp(N-BigInt(k-j),p));
  }
  for(let j=0;j<k;j++)check(small[j]>=BigInt(B)&&small[j]%BigInt(wanted[j])===0n,
      "all lifted positions lose their covering divisors");
  cases++;
}
for(const Q of [3,5,7,11])for(const H of [27,48,71]){
  const K=301;
  const starts=Array.from({length:200},(_,i)=>K+i).filter(k=>k%Q===0);
  const hs=Array.from({length:H-1},(_,i)=>i+1).filter(h=>h%Q===Q-1);
  let one=0,two=0,ord=0;
  for(const k of starts){
    const r=primes.filter(p=>k-H<p&&p<k&&p%Q===1).length;
    one+=r;two+=r*r;
  }
  let reverse=0;
  for(const h of hs){
    reverse+=starts.filter(k=>spf[k-h]===k-h).length;
    for(const h2 of hs)if(h!==h2)
      ord+=starts.filter(k=>spf[k-h]===k-h&&spf[k-h2]===k-h2).length;
  }
  check(one===reverse&&two===reverse+ord,"first and second moment count switch");
  mixedMoments++;
}
console.log(JSON.stringify({checks,cases,usedReserves,mixedMoments,examples}));
