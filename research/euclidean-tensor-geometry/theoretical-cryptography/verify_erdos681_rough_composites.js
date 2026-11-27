"use strict";
// Exact finite checks of occupancy, CRT errors, and moment inversion.
let checks=0, draws=0, tPositions=0, inversions=0;
function ok(cond, msg) {
  ++checks;
  if(!cond) throw Error(msg);
}
function pop(a) { let j=0; for(;a;a&=a-1)++j; return j; }
function normal(a,p) { return (a%p+p)%p; }
function occupancy(primes,r,offsets,primePredecessor=false) {
  const N=primes.reduce((a,b)=>a*b,1);
  const counts=new Int32Array(1<<r);
  for(let a=0;a<N;++a) {
    if(primePredecessor&&primes.some(p=>(a+1)%p===0)) continue;
    ++draws;
    let mask=0;
    for(const p of primes) for(let i=0;i<r;++i) if((a+offsets[i])%p===0) mask|=1<<i;
    ++counts[mask];
  }
  const choices=primes.map(p=>p-Number(primePredecessor));
  const total=choices.reduce((a,b)=>a*BigInt(b),1n);
  ok(BigInt(counts.reduce((a,b)=>a+b,0))===total,"number of (possibly reduced) residue choices");
  for(let A=0;A<(1<<r);++A) {
    const d=pop(A);
    let none=0n, all=0n;
    for(let m=0;m<(1<<r);++m) {
      if((m&A)===A) all+=BigInt(counts[m]);
      if((m&A)===0) none+=BigInt(counts[m]);
    }
    let singleNo=1n;
    for(const p of choices) singleNo*=BigInt(p-1);
    ok(none===choices.reduce((x,p)=>x*BigInt(p-d),1n),"no-hit occupancy formula");
    if(d>0) {
      ok(none*total**BigInt(d-1)<=singleNo**BigInt(d),"unhit product bound");
      ok(all*total**BigInt(d-1)<=(total-singleNo)**BigInt(d),"hit product bound");
    }
  }
}
for(const ps of [[5,7],[7,11,13],[11,13,17,19]]) {
  for(let r=1;r<=Math.min(ps[0]-1,7);++r) {
    for(let offset=1;offset<=3;++offset) occupancy(ps,r,Array.from({length:r},(_,i)=>offset+i));
  }
}
for(const ps of [[5,7],[7,11,13],[11,13,17,19]]) {
  for(let r=1;r<=Math.min(ps[0]-2,7);++r)
    occupancy(ps,r,Array.from({length:r},(_,i)=>i+2),true);
}
const ps=[5,7,11,13], modulus=ps.reduce((x,p)=>x*p,1);
const r=3, offsets=[2,3,4], dim=2*r, full=1<<dim;
function test(a,Q,left,H) {
  const exact=new Int32Array(full);
  const actualFamily=Array.from({length:full},()=>new Int32Array(1<<ps.length));
  for(let t=left;t<left+H;++t) {
    ++tPositions;
    let M=(1<<dim)-1;
    const n=a+Q*t;
    const affected=[];
    for(let j=0;j<ps.length;++j) {
      const stage=+(j>=2), p=ps[j];
      let bits=0;
      for(let i=0;i<r;++i) if(normal(n+offsets[i],p)===0) bits|=1<<(stage*r+i);
      affected.push(bits); M&=~bits;
    }
    exact[M]++;
    for(let A=0;A<full;++A) {
      let bad=0;
      for(let j=0;j<ps.length;++j) if((A&affected[j])!==0) bad|=1<<j;
      ++actualFamily[A][bad];
    }
  }
  const moments=new Int32Array(full);
  for(let A=0;A<full;++A) {
    for(let M=0;M<full;++M) if((M&A)===A) moments[A]+=exact[M];
    const dist=actualFamily[A];
    ok(moments[A]===dist[0],"zero events equals the all-ones moment");
    const deg=[pop(A&7),pop(A>>r)];
    const level=new Int32Array(ps.length+1);
    const randomLevel=new Int32Array(ps.length+1);
    for(let J=0;J<(1<<ps.length);++J) {
      let actual=0, q=1, nu=1;
      for(let j=0;j<ps.length;++j) if(J>>j&1) {
        q*=ps[j]; nu*=deg[+(j>=2)];
      }
      for(let bad=0;bad<dist.length;++bad) if((bad&J)===J) actual+=dist[bad];
      ok(Math.abs(actual*q-H*nu)<=nu*q,"CRT error at a finite interval endpoint");
      level[pop(J)]+=actual;
      randomLevel[pop(J)]+=nu*(modulus/q);
    }
    const model=ps.reduce((x,p,j)=>x*(p-deg[+(j>=2)]),1);
    let total=0, randomTotal=0;
    for(let degree=0;degree<=ps.length;++degree) {
      const sign=degree%2?-1:1;
      total+=sign*level[degree];randomTotal+=sign*randomLevel[degree];
      ok(sign*(total-moments[A])>=0,"Bonferroni parity for the arithmetic interval");
      ok(sign*(randomTotal-model)>=0,"Bonferroni parity for independent prime residues");
    }
    ok(total===moments[A]&&randomTotal===model,"all orders give exact counts");
  }
  for(let A=0;A<full;++A) {
    const z=(full-1)^A;
    let sum=0;
    for(let J=z;;J=(J-1)&z) {
      sum+=(pop(J)%2?-1:1)*moments[A|J];
      if(J===0) break;
    }
    ++inversions;
    ok(sum===exact[A],"Möbius inversion of an actual interval's bit law");
  }
}
for(const Q of [1,2,3,6]) for(let a=0;a<Q;++a)
  for(const left of [-18,0,42]) for(const H of [8,23,122,997])test(a,Q,left,H);
for(let K=2;K<=20;++K) {
  const small=[2,3,5,7,11,13,17,19].filter(p=>p<=K), Q=small.reduce((x,p)=>x*p,1);
  for(let j=1;j<=10;++j) for(let k=2;k<=K;++k) {
    const p=small.find(p=>k%p===0);
    ok(p<=k&&(j*Q+k)%p===0,"primorial obstruction to shift k >= 2");
  }
}
console.log(JSON.stringify({assertions:checks,primeResidueTuples:draws,intervalPositions:tPositions,inversions}));
