"use strict";

// Exact small-fixture checks, not a test of asymptotic gap hypotheses.
// Run: node verify_factor_erdos912_gap_phase.js
const lim=4500;
const flag=new Uint8Array(2*lim+50).fill(1);
flag[0]=flag[1]=0;
for(let p=2;p*p<flag.length;++p) if(flag[p]) 
  for(let i=p*p;i<flag.length;i+=p) flag[i]=0;
const primes=[];
for(let p=2;p<flag.length;++p) if(flag[p]) primes.push(p);
let checks=0, pairTerms=0, blocks=0;
const check=(condition,label)=>{++checks;if(!condition) throw Error(label);};
const fl=(x,y)=>Math.floor(x/y);
function legendre(n,p) {
  let v=0;
  while(n>=p) { n=fl(n,p);v+=n; }
  return v;
}
for(let n=1;n<=lim;++n) {
  const v=new Set(), f=new Set();
  let transitions=0, tails=0;
  const cutoff=2+(n%251);
  let firstAbove=0;
  for(let i=0;primes[i]<=n;++i) {
    const p=primes[i],q=primes[i+1],prod=p*q,g=q-p;
    v.add(legendre(n,p));
    const x=fl(n,p),y=fl(n,q);
    f.add(x);
    const d=+(x>y);
    // Scale (4) by pq so both sides are integers.
    const scaledSmooth=Math.min(prod,n*g);
    const rhs=n*g<prod ? p*(n%q)-q*(n%p):0;
    check(prod*d-scaledSmooth===rhs,"local indicator/phase");
    if(n*g<prod)check(x-y===0||x-y===1,"unsaturated floor difference");
    transitions+=d;
    if(p>cutoff) {tails+=d;if(!firstAbove)firstAbove=p;}
    ++pairTerms;
  }
  check(v.size===f.size&&f.size===transitions,"factorial-floor-gap identity");
  if(firstAbove)check(tails<=fl(n,firstAbove),"indicator tail");
}
// First primes at most P, plus their next prime for rational scaling.
function blockTest(X,H,P) {
  const ks=primes.findIndex(p=>p>P);
  const qs=primes.slice(0,ks+1);
  const D=2n*qs.reduce((a,q)=>a*BigInt(q),1n);
  const w=qs.map(q=>D/(2n*BigInt(q)));
  const z=(i,n)=>BigInt(2*(n%qs[i])-(qs[i]-1))*w[i];
  const map=new Map();
  const endpoints=[];
  for(let i=0;i<ks;++i) {
    const p=qs[i],q=qs[i+1];
    // n<T iff n <= floor((pq-1)/(q-p)) for integer n.
    const K=Math.max(0,Math.min(H,fl(p*q-1,q-p)-X+1));
    endpoints.push(K);
    const sizes=[];
    let left=0;
    for(let b=2**fl(Math.log2(H),1);b>=1;b/=2) if(K&b) {
      check(left%b===0&&!sizes.includes(b),"anchored dyadic block");
      sizes.push(b);
      const id=left+":"+b;
      if(!map.has(id))map.set(id,{left,b,ids:[]});
      map.get(id).ids.push(i);
      left+=b;
    }
    check(left===K,"dyadic decomposition length");
    for(let s=0;s<H;++s)
      check((s<K)===((X+s)*(q-p)<p*q),"prefix membership");
  }
  const viaBlocks=Array(H).fill(0n);
  for(const {left,b,ids} of map.values()) {
    let square=0n;
    const multiplicity=Array(qs.length).fill(0);
    for(const i of ids) {--multiplicity[i];++multiplicity[i+1];}
    check(multiplicity.every(x=>Math.abs(x)<=1),"collected coefficients");
    for(let s=left;s<left+b;++s){
      let v=0n;
      for(const i of ids) v+=z(i+1,X+s)-z(i,X+s);
      viaBlocks[s]+=v;
      square+=v*v;
    }
    const Q=qs[qs.length-1];
    check(6n*square<=BigInt((b+Q*Q)*ids.length)*D*D,"finite block large sieve bound");
    ++blocks;
  }
  for(let s=0;s<H;++s) {
    let e=0n, uncentered=0n, bias=0n;
    for(let i=0;i<ks;++i) if(s<endpoints[i]) {
      const p=qs[i],q=qs[i+1],n=X+s;
      e+=z(i+1,n)-z(i,n);
      uncentered+=BigInt(n%q)*D/BigInt(q)-BigInt(n%p)*D/BigInt(p);
      bias+=w[i]-w[i+1];
    }
    check(e===viaBlocks[s]&&e+bias===uncentered,"centered phase assembly");
    check(0n<=bias&&4n*bias<=D,"bounded reciprocal bias");
  }
  for(let i=0;i<qs.length;++i) {
    const q=qs[i];
    let sum=0n,square=0n;
    for(let j=0;j<q;++j){const v=z(i,j);sum+=v;square+=v*v;}
    check(sum===0n&&12n*BigInt(q)*square===BigInt(q*q-1)*D*D,"Parseval energy");
  }
  const freq=[];
  for(const q of qs)for(let a=1;a<q;++a)freq.push([a,q]);
  freq.sort(([a,q],[b,r])=>a*r-b*q);
  const Q=qs[qs.length-1];
  for(let i=0;i<freq.length;++i){
    const [a,q]=freq[i],[b,r]=freq[(i+1)%freq.length];
    const gap=b*q-a*r+(i===freq.length-1?q*r:0);
    check(gap>0&&gap*Q*Q>=q*r,"cyclic frequency spacing");
  }
}
for(const [X,H,P] of [[3,1,2],[8,8,8],[57,55,23],[180,7,31],
                       [500,300,71],[1024,1000,97],[1200,999,103],
                       [2700,950,130],[4000,417,169]]) blockTest(X,H,P);
console.log("PASS: "+checks+" exact assertions, "+pairTerms+
            " consecutive-prime local identities, "+blocks+" dyadic blocks, n<=4500");
