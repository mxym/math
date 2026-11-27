"use strict";

// All tested grids are fixed lists of known tiny primes. This checks
// covering matrices and never accepts an unknown product as input.
function cells(P) {
  const out=[];
  for(let i=0;i<P.length;i++) for(let j=i+1;j<P.length;j++)
    out.push({i,j,p:P[i],q:P[j],n:P[i]*P[j]});
  return out;
}
let checks=0,crosses=0,certs=0,profiles=0;
function ok(x,msg) { checks++; if(!x) throw Error(msg); }
function power(x,k) { return BigInt(x)**BigInt(k); }
function makeBins(P,H) {
  const width=P[0]*H, buckets=new Map();
  for(const a of cells(P)) {
    a.b=Math.floor((a.p-P[0])/H);
    a.jj=Math.floor((a.n-P[0]**2)/width);
    if(!buckets.has(a.jj)) buckets.set(a.jj,[]);
    buckets.get(a.jj).push(a);
  }
  return {width,buckets};
}
function diamTuples(P,H,r) {
  let c=0n;
  for(let i=0;i<P.length;i++) {
    const m=P.slice(i).filter(p=>p<=P[i]+H).length;
    c+=power(m,r)-power(m-1,r);
  }
  return c;
}
function moments(band,r) {
  const n=new Map();
  for(const a of band)n.set(a.b,(n.get(a.b)||0)+1);
  return [...n.values()].reduce((s,t)=>s+power(t,r),0n);
}
const primes=[107,109,113,127,131,137,139,149,151,157,163,167,173,179,
              181,191,193,197,199,211];
for(const H of [1,3,5,8,12]) {
  const {width,buckets}=makeBins(primes,H);
  for(let r=2;r<=5;r++) {
    const sum=[...buckets.values()].reduce((s,j)=>s+moments(j,r),0n);
    ok(sum<=diamTuples(primes,H,r)*diamTuples(primes,3*H,r),
       "global moment bound");
  }
  for(const group of buckets.values()) for(const target of group) {
    for(const sign of [-1,1]) {
      const near=group.filter(a=>sign*(a.n-target.n)>0);
      const byParity=[new Map(),new Map()];
      for(const a of near)byParity[a.b%2].set(a.b,a);
      for(const map of byParity) {
        const list=[...map.values()].sort((u,v)=>u.p-v.p);
        for(let i=0;i<list.length;i++) for(let j=i+1;j<list.length;j++) {
          const a=list[i], b=list[j];
          ok(b.p-a.p>H && a.q>b.q && b.p<a.q && a.p<b.q,
             "crossed cells valid in triangular promise");
          ok(sign<0 ? b.p*a.q>target.n : a.p*b.q<target.n,
             "crossed cell on the opposite side");
          ok(b.p*a.q-a.n>width,"whole-band gap");
          crosses++;
        }
      }
      const f=Math.max(...byParity.map(m=>m.size));
      for(let r=2;r<=5;r++)
        ok(power(near.length,r)<=power(2*f,r-1)*moments(group,r),
           "same-band rank bound");
      profiles++;
    }
  }
}

// Exact tiny cover optimization. A row subset may use all columns that
// satisfy the sign on its valid cells, which gives a maximal rectangle.
function exactSmallCover(P,target,sign) {
  const all=cells(P), good=all.filter(a=>sign*(a.n-target)>0);
  const full=(1<<good.length)-1, masks=new Set();
  for(let rows=1;rows<1<<P.length;rows++) {
    let mask=0;
    for(let j=0;j<P.length;j++) {
      if(all.some(a=>a.j===j&&(rows&(1<<a.i))&&sign*(a.n-target)<=0))continue;
      for(let k=0;k<good.length;k++)
        if(good[k].j===j&&(rows&(1<<good[k].i)))mask|=1<<k;
    }
    if(mask)masks.add(mask);
  }
  const memo=new Map();
  function cover(state,k) {
    if(!state)return 0;
    const key=4*state+k;
    if(memo.has(key))return memo.get(key);
    const first=state&-state;
    let ans=k ? cover(state^first,k-1) : good.length;
    for(const w of masks) if(w&first) ans=Math.min(ans,1+cover(state&~w,k));
    memo.set(key,ans);
    return ans;
  }
  return [cover(full,0),cover(full,1),cover(full,2)];
}
const little=[53,67,71,79,83,101];
for(const target of cells(little)) for(const sign of [-1,1]) {
  const exact=exactSmallCover(little,target.n,sign);
  ok(exact[0]<=little.length,"row cover upper bound");
  for(const H of [1,8,20]) {
    const {width,buckets}=makeBins(little,H);
    const group=buckets.get(Math.floor((target.n-little[0]**2)/width));
    const rank=group.filter(a=>sign*(a.n-target.n)>0).length;
    for(let k=0;k<=2;k++) for(let r=2;r<=4;r++) {
      ok(power(Math.max(0,rank-k),r)<=power(2*exact[k],r-1)*moments(group,r),
         "omission-tolerant inequality against exact tiny cover");
      certs++;
    }
  }
}
console.log("OK: "+checks+" exact checks, "+crosses+" crossed-cell pairs, "+
            profiles+" rank profiles, "+certs+" exact-cover comparisons.");
