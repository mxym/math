'use strict';
/* Small exact checks of the paper's array identities and exceptional count.
 * No imports beyond built-in assertions; generated integer toy root arrays only. */
const assert=require('node:assert/strict');
let checks=0;function check(a,b){assert.deepEqual(a,b);checks++;}
const range=n=>Array.from({length:n},(_,i)=>i);
const sum=a=>a.reduce((s,x)=>s+x,0);
const norm=a=>sum(a.map(x=>x*x));
const zero=n=>Array(n).fill(0);
function prod(a){return a.reduce((p,v)=>p*v,1);}
function words(ns){return ns.reduce((v,n)=>v.flatMap(w=>range(n).map(j=>[...w,j])),[[]]);}
function boxes(qs){
  return words(qs.map(q=>q-1)).map(b=>{
    const path=b.map(x=>x+1);
    return words(qs).map(w=>prod(w.map((x,i)=>x===0?1:x===path[i]?-1:0)));
  });
}
function add(a,b,m=1){return a.map((x,i)=>x+m*b[i]);}
function lin(coeff,B){return coeff.reduce((x,t,i)=>add(x,B[i],t),zero(B[0].length));}
function eAgree(b,c){return b.filter((x,j)=>x===c[j]).length;}
function marginalSquares(coeff,qs){
  const k=qs.length,W=words(qs.map(q=>q-1));
  let energy=0;
  for(let mask=0;mask<1<<k;mask++){
    const bins=new Map();
    for(let b=0;b<W.length;b++){
      const key=W[b].filter((_,j)=>mask>>j&1).join(',');
      bins.set(key,(bins.get(key)||0)+coeff[b]);
    }
    energy+=norm([...bins.values()]);
  }
  return energy;
}
function rng(seed){return ()=>{seed=(1664525*seed+1013904223)>>>0;return seed;};}
const rnd=rng(33311);
for(const qs of [[3],[4],[3,3],[3,4],[3,3,3],[3,4,3],[5,3,4],[3,3,3,3]]){
  const B=boxes(qs),W=words(qs.map(q=>q-1));
  for(let j=0;j<B.length;j++)for(let i=0;i<B.length;i++){
    check(sum(B[j].map((x,h)=>x*B[i][h])),2**eAgree(W[j],W[i]));
  }
  for(let c=0;c<60;c++){
    const C=B.map(()=>rnd()%7-3),f=lin(C,B);
    check(f[0],sum(C));check(norm(f),marginalSquares(C,qs));
    const k=qs.length,Z=words(qs);
    for(let d=0;d<k;d++){
      const s=new Map();
      for(let i=0;i<f.length;i++){
        const key=Z[i].filter((_,j)=>j!==d).join(',');s.set(key,(s.get(key)||0)+f[i]);
      }
      check([...s.values()].every(x=>x===0),true);
    }
  }
}
// Exhaust independently all k=2 anchored arrays in the checked energy window.
// Each independent coefficient is itself, up to sign, an array cell, so its
// squared value individually and collectively cannot exceed the energy.
function listTwo(qs,limit){
  assert.equal(qs.length,2);
  const dim=prod(qs.map(q=>q-1)),B=boxes(qs),by=new Map();
  function rec(c,rem){
    if(c.length===dim){
      const f=lin(c,B),Q=norm(f);
      if(Q>limit)return;
      if(!by.has(f[0]))by.set(f[0],[]);
      by.get(f[0]).push({f,Q,c});
      return;
    }
    const l=Math.floor(Math.sqrt(rem));
    for(let a=-l;a<=l;a++)rec([...c,a],rem-a*a);
  }
  rec([],limit);return by;
}
function select(base,a,limit){return (base.get(a)||[]).filter(x=>x.Q<=limit);}
const D2=listTwo([3,3],48),D24=listTwo([3,4],26);
for(const [A,m1,m2,m3,n3] of [[D2,4,10,22,4],[D24,4,10,20,6]]){
  const av=a=>[...A.get(a)].sort((x,y)=>x.Q-y.Q);
  check(av(1)[0].Q,m1);check(av(2)[0].Q,m2);check(av(3)[0].Q,m3);
  check(av(3).filter(x=>x.Q===m3).length,n3);
}
function coarse(k,a,p=0){
  a=Math.abs(a);return a*2**k+a*a-a+(a===3?2*p:0);
}
function extendTernary(k,source,a,cap){
  const out=[];
  for(let b=-Math.floor(Math.sqrt(cap));b<=Math.floor(Math.sqrt(cap));b++){
    const c=-a-b;
    const loA=coarse(k-1,a,k-1),loB=coarse(k-1,b,k-1),loC=coarse(k-1,c,k-1);
    if(loA+loB+loC>cap)continue;
    for(const A of source(a,cap-loB-loC))for(const B of source(b,cap-A.Q-loC)){
      const fC=A.f.map((x,i)=>-x-B.f[i]),qC=norm(fC),Q=A.Q+B.Q+qC;
      if(Q<=cap){assert.equal(fC[0],c);out.push({f:A.f.concat(B.f,fC),Q});}
    }
  }
  return out;
}
const S2=(a,l)=>select(D2,a,l);
const cache=new Map();
function S3(a,l){
  // These independent tests have k=3 lookup limits no larger than 48.
  if(l>48)throw Error('increase exact base table cap');
  const key=a+','+l;if(!cache.has(key))cache.set(key,extendTernary(3,S2,a,l));return cache.get(key);
}
const Z3=S3(3,38);
check(Math.min(...Z3.map(x=>x.Q)),36);
check(Z3.filter(x=>x.Q===36).length,8);
check(S3(2,19).map(x=>x.Q).every(q=>q===18),true);
check(S3(2,19).length,4);
const Z4=extendTernary(4,S3,3,64);
check(Math.min(...Z4.map(x=>x.Q)),64);check(Z4.length,112);
const altFocal=words([3,3,3,3]).flatMap((w,i)=>w.every(x=>x!==0)?[i]:[]);
const ordinary=Z4.filter(x=>altFocal.every(i=>x.f[i]>=0));
const exceptional=Z4.filter(x=>altFocal.some(i=>x.f[i]<0));
check(ordinary.length,96);check(exceptional.length,16);
check(new Set(Z4.map(t=>t.f.join(','))).size,112);
for(const v of exceptional){
  const c=altFocal.map(i=>v.f[i]);check(c.filter(x=>x===-1).length,1);
  check(c.filter(x=>x===1).length,4);check(sum(c),3);
}
function C(n,k){if(k<0||k>n)return 0;let p=1;for(let j=1;j<=k;j++)p=p*(n-j+1)/j;return p;}
function e3(p){return 2**(Math.floor(p/3)+1)*(3+p%3);}
for(const qs of [[3],[4],[3,3],[3,4],[3,3,3],[3,3,3,3],[3,4,3]]){
  const k=qs.length,p=qs.filter(x=>x===3).length,m=prod(qs.map(x=>x-1)),B=boxes(qs);
  let best=Infinity,cnt=0;
  for(let i=0;i<m;i++)for(let j=i;j<m;j++)for(let h=j;h<m;h++){
    const f=add(add(B[i],B[j]),B[h]),Q=norm(f);
    if(Q<best){best=Q;cnt=1;}else if(Q===best)cnt++;
  }
  const d=Math.floor(p/3),s=p%3,F=n=>prod(range(n).map(j=>j+1));
  const formula=k===1?(qs[0]===3?2:C(qs[0]-1,3)):
    C(3,s)*F(p)/F(d+1)**s/F(d)**(3-s)*2**p*
    prod(qs.filter(q=>q>=4).map(q=>(q-1)*(q-2)*(q-3)))/6;
  check(best,3*2**k+e3(p));check(cnt,formula);
}
// Count all unanchored two-box vectors with genuinely nonunit coefficients
// and within the written strict threshold (toy k=1..3 mixed fixtures).
for(const qs of [[3],[4],[3,3],[3,4],[3,3,3]]){
  const k=qs.length,axes=qs.map(q=>range(q).flatMap(i=>range(q).filter(j=>i<j).map(j=>[i,j])));
  const W=words(qs),choices=words(axes.map(a=>a.length));
  const B=choices.map(v=>W.map(w=>prod(w.map((x,i)=>x===axes[i][v[i]][0]?1:x===axes[i][v[i]][1]?-1:0))));
  const counts=new Map(),seen=new Set();
  for(let i=0;i<B.length;i++)for(let j=i+1;j<B.length;j++)for(const a of [-1,1])for(const b of [-1,1]){
    const f=B[i].map((x,w)=>a*x+b*B[j][w]),Q=norm(f);
    if(f.every(x=>Math.abs(x)<2)||Q>=(9/4)*2**k+2)continue;
    const key=f.join(',');assert(!seen.has(key));seen.add(key);
    counts.set(Q,(counts.get(Q)||0)+1);
  }
  for(let t=0;t<k;t++){
    const Q=2*2**k+2**(t+1);let theory=0;
    if(Q<(9/4)*2**k+2)for(let mask=0;mask<1<<k;mask++){
      if(range(k).filter(j=>mask>>j&1).length!==t)continue;
      theory+=prod(qs.map((q,j)=>mask>>j&1?q*(q-1)/2:q*(q-1)*(q-2)));
    }
    check(counts.get(Q)||0,theory);
  }
}
console.log('PASS: '+checks+' exact checks; exceptional anchored norm 64 count = 112 (96 ordinary + 16 signed)');
