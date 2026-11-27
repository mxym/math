"use strict";
// Fixed primorial fixtures. Tests finite counting and repairs, not the
// asymptotic cover theorem or its constant.
const assert=(ok,m)=>{if(!ok)throw Error(m);};
const mod=(a,p)=>(a%p+p)%p;
const bigmod=(a,p)=>(a%p+p)%p;
const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a;};
const bgcd=(a,b)=>{while(b!==0n)[a,b]=[b,a%b];return a;};
const inv=(a,m)=>{
  let [x,y,u,v]=[a,m,1n,0n];
  while(y!==0n){const q=x/y;[x,y,u,v]=[y,x-q*y,v,u-q*v];}
  assert(x===1n,"invertible CRT modulus");
  return bigmod(u,m);
};
function crt(classes){
  let t=0n,M=1n;
  for(const [p,b] of classes){
    const P=BigInt(p), residue=BigInt(mod(-b,p));
    t+=M*bigmod((residue-t)*inv(M%P,P),P);
    M*=P;
  }
  assert(0n<=t&&t<M,"CRT range");
  for(const [p,b] of classes)assert(bigmod(t+BigInt(b),BigInt(p))===0n,"CRT local congruence");
  return [t,M];
}
const range=(a,b)=>Array.from({length:b-a+1},(_,i)=>a+i);
const base=[2,3,5,7,11,13], reserveA=[17,19,23,29,31,37,41,43,47,53,59,61,67,71];
const fixtures=[];
for(const t0 of [9439,30030-9461,1,13]){
  let Y=0;while(Y<30&&base.some(p=>(t0+Y+1)%p===0))Y++;
  if(Y>=5)fixtures.push({Y,classes:base.map(p=>[p,mod(-t0,p)]),reserve:reserveA});
}
// For protected points 1 and 21, the class at 7 is deliberately the
// only old coverage of 15. This fixture forces an interior repair.
const C0=[[2,0],[3,2],[5,2],[7,1],[11,10],[13,0]];
let addAt=0;const extras=[23,29,31,37,41,43,47,53,59,61,67,71];
for(const n of range(1,21))if(!C0.some(([p,b])=>n%p===b)){
  const p=extras[addAt++];C0.push([p,n%p]);
}
fixtures.push({Y:21,classes:C0,reserve:[73,79,83,89,97,101,103,107,109,113,127,131]});
let originalCover=0,smallSieve=0,individualCounts=0,coverLoss=0,repair=0,completion=0;
for(const {Y,classes,reserve} of fixtures){
  const validity=[...classes.map(([p])=>p),...reserve];
  const admissible=h=>validity.every(p=>new Set(h.map(v=>mod(v,p))).size<p);
  for(const n of range(1,Y)){assert(classes.some(([p,b])=>n%p===b),"old full cover");originalCover++;}
  const offsets=[];
  for(let h=2;h<=Y-1;h+=2){
    offsets.push([0,h]);
    for(let d=2;d<h;d+=2)if(admissible([0,d,h]))offsets.push([0,d,h]);
  }
  const small=classes.slice(0,3), large=classes.slice(3);
  for(const hs of offsets) {
    assert(admissible(hs),"given offsets admissible");
    const M=Y-hs[hs.length-1], trial=range(1,M);
    const hit=(m,p,b)=>hs.some(h=>(m+h)%p===b);
    const allowed=trial.filter(m=>small.every(([p,b])=>!hit(m,p,b)));
    for(let mask=0;mask<2**small.length;mask++){
      let product=1,nu=1;const A=[];
      for(let j=0;j<small.length;j++)if((mask>>j)&1){
        const [p,b]=small[j];A.push([p,b]);product*=p;nu*=new Set(hs.map(h=>mod(b-h,p))).size;
      }
      const full=range(1,product).filter(m=>A.every(([p,b])=>hit(m,p,b))).length;
      assert(full===nu,"CRT count of forbidden intersections");
      const actual=trial.filter(m=>A.every(([p,b])=>hit(m,p,b))).length;
      assert(Math.abs(product*actual-M*nu)<=product*nu,"truncated count error");
      individualCounts+=2;
    }
    for(let J=1;J<=3;J+=2){
      let B=0;
      for(let mask=0;mask<2**small.length;mask++){
        const A=small.filter((_,i)=>(mask>>i)&1);if(A.length>J)continue;
        B+=(-1)**A.length*trial.filter(m=>A.every(([p,b])=>hit(m,p,b))).length;
      }
      assert(B<=allowed.length,"odd Bonferroni lower bound");smallSieve++;
    }
    if(!allowed.length)continue;
    const counts=allowed.map(m=>{
      const remaining=classes.filter(([p,b])=>!hit(m,p,b));
      const uncovered=range(1,Y).filter(n=>!remaining.some(([p,b])=>n%p===b));
      for(const h of hs) assert(uncovered.includes(m+h),"protected point uncovered");
      return {m,remaining,uncovered};
    });
    const sumA=counts.reduce((z,x)=>z+x.uncovered.length,0);
    let bound=0;
    for(const [p,b] of large){
      const c=allowed.filter(m=>hit(m,p,b)).length;
      assert(c<=hs.length*(Math.floor(M/p)+1),"large prime collision count");
      bound+=c*range(1,Y).filter(n=>n%p===b).length;
    }
    assert(sumA<=bound,"deletion union bound");coverLoss++;
    const val=counts.reduce((a,b)=>a.uncovered.length<b.uncovered.length?a:b);
    assert(val.uncovered.length*allowed.length<=bound,"averaged shift");
    // Test every allowed shift as a finite repair fixture, not only the
    // optimization witness. The reserve is large enough on these fixtures.
    for(const entry of counts) {
    const {m}=entry, protect=hs.map(h=>m+h), end=protect[protect.length-1];
    const needed=entry.uncovered.filter(n=>m<n&&n<end&&!protect.includes(n));
    const chosen=new Map(entry.remaining);
    for(const n of needed){
      const bad=reserve.filter(p=>protect.some(v=>mod(n-v,p)===0));
      assert(bad.length<=hs.length,"each position excludes at most r reserve primes");
      const p=reserve.find(p=>!bad.includes(p)&&!chosen.has(p));
      assert(p!==undefined,"greedy step succeeds");
      chosen.set(p,n%p);repair++;
    }
    const unassigned=validity.filter(p=>!chosen.has(p));
    const qa=unassigned.filter(p=>reserve.includes(p));
    assert(qa.length>=2,"two reserve choices remain");
    const P=qa[qa.length-1], Q=qa[qa.length-2];
    const choices=p=>range(0,p-1).filter(b=>protect.every(n=>n%p!==b));
    for(const p of unassigned)if(p!==P&&p!==Q)chosen.set(p,choices(p)[0]);
    const orbit=new Set();let inside=0;
    for(const a of choices(P).slice(0,3))for(const b of choices(Q).slice(0,3)){
      chosen.set(P,a);chosen.set(Q,b);
      const [t,N]=crt(chosen);
      const u=(t+BigInt(m))%N;
      assert(!orbit.has(u.toString()),"different residues give different block start");
      orbit.add(u.toString());
      const isInside=u>0n&&u+BigInt(end-m)<N;
      if(isInside)inside++;
      for(let i=0;i<=end-m;i++)
        assert((bgcd(N,(u+BigInt(i))%N)===1n)===hs.includes(i),"final exact coprime pattern");
      completion++;
    }
    assert(inside>0,"finite-list placements");
    }
  }
}
assert(repair>0,"fixtures exercised interior repair");
let incompatibility=0, nontrivial=0;
for(const n of range(1,550))if(![1,124,207].includes(n)){
  const bad=[41,43,47,53,59,61,67,71,73].filter(p=>[1,124,207].some(a=>(n-a)%p===0));
  assert(bad.length<=3,"reserve collision at a nonzero bounded difference");
  if(bad.length)nontrivial++;
  incompatibility++;
}
assert(nontrivial>0,"fixtures exercised forbidden reserve choices");
console.log({originalCover,smallSieve,individualCounts,coverLoss,repair,completion,incompatibility,
             total:originalCover+smallSieve+individualCounts+coverLoss+repair+completion+incompatibility});
