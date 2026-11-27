"use strict";
// Exact identities on generated toy distributions; no samples/keys/estimators.
const check=(a,b)=>{if(a!==b)throw Error(a+" != "+b);};
const q=3, mod=x=>(x%q+q)%q;
const weights=[2,1,0];
const enumerate=(dims,fn)=>{
  function go(x,w){if(x.length===dims){fn(x,w);return;}
    for(let a=0;a<q;++a)if(weights[a])go([...x,a],w*BigInt(weights[a]));
  }go([],1n);
};
const conv=(sgn)=>{
  const out=Array(q).fill(0n);
  enumerate(sgn.length,(x,w)=>{out[mod(x.reduce((s,t,i)=>s+t*sgn[i],0))]+=w;});
  return out;
};
const plus=conv([1,1]), minus=conv([1,-1]);
const direct=Array(q*q).fill(0n);
enumerate(4,([a,b,c,d],w)=>{direct[mod(a-d)*q+mod(b+c)]+=w;});
for(let i=0;i<q*q;++i)check(direct[i],minus[Math.floor(i/q)]*plus[i%q]);
function chiNumer(a){const n=a.reduce((p,x)=>p+x,0n);return BigInt(a.length)*a.reduce((a,x)=>a+x*x,0n)-n*n;}
check(plus.join(","),"4,4,1");check(minus.join(","),"5,2,2");
check(chiNumer(plus),18n);check(chiNumer(minus),18n);check(chiNumer(direct),3240n);
// Direct two-fold boundary: disjoint rows factor, overlapping rows need not.
const paired=(overlap)=>{
  const mat=Array(q*q).fill(0n);
  enumerate(overlap?3:4,(x,w)=>{mat[mod(x[0]+x[1])*q+mod((overlap?x[0]:x[2])+(overlap?x[2]:x[3]))]+=w;});
  return mat;
};
const djoint=paired(false), ojoint=paired(true);
for(let i=0;i<q*q;++i)check(djoint[i],plus[Math.floor(i/q)]*plus[i%q]);
check(ojoint[0],8n); // For the overlap, P(0,0)=8/27 vs 16/81 for disjoint folds.
console.log({negacyclicLaw:direct.map(String),disjointChiNumer:String(chiNumer(djoint)),overlap00:String(ojoint[0])});
