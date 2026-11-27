"use strict";
// Exact checks for the finite algebra in the #468 divisor-prefix proof.
// No dependencies. These examples do not test the analytic sieve theorem.
let checks=0, cases=0, triples=0, maximumHits=0, example=null;
const ok=(b,msg)=>{++checks;if(!b)throw Error(msg);};
const prod=(xs)=>xs.reduce((a,b)=>a*b,1n);
const prime=(n)=>{
  if(n<2n)return false;
  for(let d=2n;d*d<=n;++d)if(n%d===0n)return false;
  return true;
};
const blockSets=[
  {M:1n,blocks:[[2n],[3n],[5n],[7n],[11n]]},
  {M:2n,blocks:[[5n],[7n],[11n],[13n],[17n]]},
  {M:30n,blocks:[[7n,11n],[13n,17n],[19n,23n]]},
  {M:15n,blocks:[[2n,3n,5n],[7n,11n],[13n],[17n]]},
];
for(const {M,blocks} of blockSets){
  const all=blocks.flat(),s=all.reduce((a,b)=>a>b?a:b,0n);
  const B=blocks.map(prod),C=blocks.map(xs=>prod(xs.map(p=>p+1n)));
  ok(all.every(prime),"block prime");
  ok(new Set(all).size===all.length,"disjoint prime support");
  const A=[M];for(const c of C)A.push(A.at(-1)*c);
  for(let ell=2n;ell<200n;++ell){
    if(!prime(ell))continue;
    // Use the nonnegative representative u=ell-1 of the class -1.
    ok(A.map(a=>a*ell-1n).every(v=>v%ell===ell-1n),"admissibility");
  }
  for(let u=1n;u<=400n;++u){
    const L=A.map(a=>a*(u+1n)-1n);
    const hits=L.map((p,i)=>[p,i]).filter(([p])=>p>s&&prime(p));
    const witnessForLargest=new Set();
    if(hits.length>=3)++triples;
    maximumHits=Math.max(maximumHits,hits.length);
    for(let a=0;a<hits.length;++a)for(let b=a+1;b<hits.length;++b){
      const [q,i]=hits[a],[p,j]=hits[b],bIJ=prod(B.slice(i,j)),D=prod(C.slice(i,j));
      ok(A[j]===A[i]*D,"slope ratio");
      ok(p%M===(M-1n)%M&&q%M===(M-1n)%M,"congruence");
      const factors=blocks.slice(i,j).flat().concat(q);
      const m=q*bIJ;
      let divisors=[1n];
      for(const f of factors)divisors=divisors.concat(divisors.map(d=>d*f));
      divisors.sort((x,y)=>x<y?-1:x>y?1:0);
      ok(new Set(divisors).size===divisors.length,"squarefree subset expansion");
      ok(divisors.at(-1)===m&&divisors[0]===1n,"endpoints");
      const sum=divisors.slice(1).reduce((x,y)=>x+y,0n);
      ok(sum===p,"last divisor-prefix");
      if(m<10000n){
        let scan=0n;
        for(let d=2n;d<=m;++d)if(m%d===0n)scan+=d;
        ok(scan===p,"independent divisor sum on a small input");
      }
      ok(p===D*(q+1n)-1n,"prime-pair identity");
      ok(m*D<p*bIJ&&m<p,"strict relative-size inequalities");
      if(b===hits.length-1){
        ok(!witnessForLargest.has(m),"distinct squarefree witness");
        witnessForLargest.add(m);
      }
      if(example===null&&hits.length>=3){
        const [lp,lj]=hits.at(-1);
        example={prime:String(lp),witnesses:hits.slice(0,-1).map(([t,i])=>String(t*prod(B.slice(i,lj))))};
      }
      ++cases;
    }
    ok(witnessForLargest.size===Math.max(0,hits.length-1),"witness count");
  }
}
ok(triples>0&&maximumHits>=3,"genuine simultaneous examples");
console.log({checks,primePairs:cases,tuplesWithAtLeastThreePrimes:triples,maximumHits,example});
