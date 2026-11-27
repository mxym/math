'use strict';



function dot(a, b) {
  return a.reduce((sum,v,i)=>sum+v*b[i],0n);
}

// Fraction-free determinant with exact row pivoting.
function det(rows) {
  const a=rows.map(row=>row.slice());
  let sign=1n, prev=1n;
  for(let j=0;j<a.length-1;j++){
    const pivot=a.findIndex((row,i)=>i>=j&&row[j]!==0n);
    if(pivot<0)return 0n;
    if(pivot!==j){[a[j],a[pivot]]=[a[pivot],a[j]];sign=-sign;}
    for(let i=j+1;i<a.length;i++)for(let k=j+1;k<a.length;k++){
      const num=a[i][k]*a[j][j]-a[i][j]*a[j][k];
      if(num%prev!==0n)throw Error('division');
      a[i][k]=num/prev;
    }
    for(let i=j+1;i<a.length;i++)a[i][j]=0n;
    prev=a[j][j];
  }
  return sign*a.at(-1).at(-1);
}
const I=Array.from({length:6},(_,i)=>i);
const E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:
  (i<5&&j<5&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===5)?-1n:0n));
const determinant=det(G);
const adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const roots=E.map(r=>r.slice()), index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){
  const r=reflect(roots[j],i);
  if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r);}
}
if(roots.length!==72)throw Error("root count");
const positive=roots.filter(r=>r.every(v=>v>=0n));
const maximal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v>=r[i])));
const minimal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v<=r[i])));
const highest=maximal(positive)[0], H=G.map(row=>dot(row,highest));
let ideals=[[]];
for(let k=0;k<7;k++){
  const next=new Map();
  for(const set of ideals)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
    const t=[...set,positive.indexOf(r)].sort((a,b)=>a-b);
    next.set(t.join(),t);
  }
  ideals=[...next.values()];
}
const groups=ideals.map(ids=>ids.map(i=>positive[i]));
const gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));
const isStar=C=>C.every((r,i)=>C.every((s,j)=>i===j||gram(r,s)===1n));

const reverse=w=>[w[4],w[3],w[2],w[1],w[0],w[5]];
const lab=C=>C.map(r=>r.join()).sort().join(';');

function vertices(C){
  const U=maximal(positive.filter(r=>!C.includes(r))), L=minimal(C);
  if(I.some(i=>!U.some(r=>r[i]>0n)))throw Error('unbounded chamber');
  const rows=[...E,...U,...L], rhs=[...I.map(()=>0n),...U.map(()=>1n),...L.map(()=>1n)], out=new Map();
  function visit(set,start){
    if(set.length<6){
      for(let i=start;i<=rows.length-6+set.length;i++)visit([...set,i],i+1);
      return;
    }
    const a=set.map(i=>rows[i]),b=set.map(i=>rhs[i]);
    let d=det(a);if(!d)return;
    const N=I.map(j=>det(a.map((r,i)=>r.map((v,k)=>j===k?b[i]:v))));
    if(d<0n){d=-d;N.forEach((v,i)=>N[i]=-v);}
    if(N.some(v=>v<0n)||U.some(r=>dot(r,N)>d)||L.some(r=>dot(r,N)<d))return;
    if(N.some(v=>12n*v%d))throw Error("rescale");
    const w=N.map(v=>12n*v/d);out.set(w.join(),w);
  }
  visit([],0);return [...out.values()];
}
const norm=k=>dot(k,adj.map(row=>dot(row,k)));
const mask=ids=>ids.reduce((b,i)=>b|(1n<<BigInt(i)),0n);
const negative=roots.map(r=>index.get(r.map(v=>-v).join()));
const moves=[...I.map(k=>r=>reflect(r,k)),reverse];
const permutations=moves.map(f=>roots.map(r=>index.get(f(r).join())));
function orbit(ids){
 const L=[ids], known=new Set([mask(ids)]);
 for(let i=0;i<L.length;i++)for(const p of permutations){
  const Y=L[i].map(j=>p[j]), m=mask(Y);
  if(!known.has(m)){known.add(m);L.push(Y);}
 }
 return L;
}

const getMask=C=>C.map(r=>index.get(r.join()));

let ideals5=[[]];
for(let k=0;k<5;k++){
  const next=new Map();
  for(const set of ideals5)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
    const t=[...set,positive.indexOf(r)].sort((a,b)=>a-b);
    next.set(t.join(),t);
  }
  ideals5=[...next.values()];
}
const groups5=ideals5.map(ids=>ids.map(i=>positive[i]));
function permutationsSmall(L){return L.length?L.flatMap((x,i)=>permutationsSmall(L.filter((_,j)=>i!==j)).map(P=>[x,...P])):[[]];}
function solve(a,b){
 let d=det(a);if(!d)throw Error("singular");
 const y=I.map(j=>det(a.map((r,i)=>r.map((v,k)=>j===k?b[i]:v))));
 if(d<0n)return {y:y.map(v=>-v),d:-d};
 return {y,d};
}
const N0=2n*determinant*144n;

function sliceHull(vs){
 const high=vs.filter(v=>norm(v)>N0), low=vs.filter(v=>norm(v)<=N0), M=96n;
 if(!high.length)return low.filter(v=>norm(v)===N0);
 const gen=high.map(U=>U.map(x=>x*M));
 for(const V of low){
  const at=(U,t)=>U.map((u,i)=>u*t+V[i]*(M-t));let t=M;
  while(high.some(U=>norm(at(U,t))>N0*M*M))t--;
  if(norm(V)===N0&&t!==0n)throw Error('sphere-level low not retained');
  for(const U of high)gen.push(at(U,t));
 }
 return [...new Map(gen.map(v=>[v.join(),v])).values()];
}
let ideals6=[[]];
for(let k=0;k<6;k++){
  const next=new Map();
  for(const set of ideals6)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
    const t=[...set,positive.indexOf(r)].sort((a,b)=>a-b);
    next.set(t.join(),t);
  }
  ideals6=[...next.values()];
}
const groups6=ideals6.map(ids=>ids.map(i=>positive[i]));


const f5=groups5.find(C=>C.every(r=>r[1]===2n)), V5=E[0].map(v=>12n*v);
const L=1152, detG=Number(determinant);
const h5=vertices(f5).filter(w=>w.join()!==V5.join()).flatMap(w=>[w.map(v=>96n*v),w.map((v,i)=>48n*(v+V5[i]))]);
const types=[f5,groups6[0],groups6[1],groups[0],groups[1],groups[2]].map((C,t)=>{
 const vs=vertices(C),h=t===0?h5:sliceHull(vs).map(w=>vs.some(v=>norm(v)>N0)?w:w.map(x=>96n*x));
 return {C,ids:getMask(C),m:mask(getMask(C)),h:h.map(x=>x.map(Number)),t,reps:new Map(), st:[], pairs:new Set(), cases:[]};
});
if(groups.length!==4||groups6.length!==3||lab(groups[0].map(reverse))!==lab(groups[3])||lab(groups6[0].map(reverse))!==lab(groups6[2]))throw Error('chamber coverage');
if(groups5.filter(isStar).length!==2||lab(groups5.filter(isStar)[0].map(reverse))!==lab(groups5.filter(isStar)[1]))throw Error('five-mask coverage');
const m=72, ini=Uint8Array.from(roots.map((_,i)=>i)), gs=[ini], gis=[ini];
const gkey=p=>((((p[0]*72+p[1])*72+p[2])*72+p[3])*72+p[4])*72+p[5];
const seen=new Set([gkey(ini)]);
for(let j=0;j<gs.length;j++){
 const p=gs[j];
 for(const q of permutations){
  const prefix=Array.from({length:6},(_,k)=>q[p[k]]),key=gkey(prefix);
  if(seen.has(key))continue;seen.add(key);
  const u=new Uint8Array(72), v=new Uint8Array(72);
  for(let i=0;i<72;i++)v[u[i]=q[p[i]]]=i;
  gs.push(u);gis.push(v);
 }
}
if(gs.length!==103680)throw Error('group count');
const bit=Array.from({length:72},(_,i)=>1n<<BigInt(i)), bitneg=negative.map(i=>bit[i]);
const pm=(ids,p)=>{let z=0n;for(const i of ids)z|=bit[p[i]];return z;};
const pneg=(ids,p)=>{let z=0n;for(const i of ids)z|=bitneg[p[i]];return z;};
const all=new Map();
for(let k=0;k<types.length;k++){
 const A=types[k];A.n=mask(A.ids.map(i=>negative[i]));
 for(let j=0;j<gs.length;j++){
  const p=gs[j], mA=pm(A.ids,p);
  if(!A.reps.has(mA)){
   if(all.has(mA))throw Error('duplicate orbit');
   const X={k,j,ids:A.ids.map(i=>p[i]),m:mA,n:pneg(A.ids,p)};
   A.reps.set(mA,X);all.set(mA,X);
  }
  if(mA===A.m)A.st.push(j);
 }
}
const rr=roots.map(r=>r.map(Number)),adjN=adj.map(r=>r.map(Number));
const dd=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3]+a[4]*b[4]+a[5]*b[5];
// Every numeric operation in the dot comparisons is an integer smaller than 2^53.
const maxAbs=xs=>Math.max(...xs.flat(Infinity).map(Math.abs));
const mxR=maxAbs(rr),mxH=maxAbs(types.flatMap(t=>t.h)),mxAdj=maxAbs(adjN);
if(36*mxR*mxH*6*mxAdj*mxH>=2**52||!types.every(t=>t.h.every(h=>h.every(Number.isSafeInteger))))throw Error('binary64 integer safety');
for(const A of types)A.dh=A.h.map(a=>adjN.map(r=>dd(r,a)));
const cutoff=-(L**2)*detG;
let edgeResults=[];
for(const A of types)for(const B of types){
 if(B.t<A.t||A.ids.length+B.ids.length>12)continue;
 let bad=new Set(), n0=0;
 for(let j=0;j<gs.length;j++){
  const p=gs[j],mb=pm(B.ids,p);if((A.m|A.n)&mb||bad.has(mb))continue;
  const inv=gis[j];let ok=false;
  for(const b of B.h){
   const y=[dd(rr[inv[0]],b),dd(rr[inv[1]],b),dd(rr[inv[2]],b),dd(rr[inv[3]],b),dd(rr[inv[4]],b),dd(rr[inv[5]],b)];
   if(A.dh.some(a=>dd(a,y)<cutoff)){ok=true;break;}
  }
  if(ok){bad.add(mb);n0++;}
 }
 const big=new Set();let nOrb=0; 
 for(const m of bad){
  if(big.has(m))continue;nOrb++;
  const b=B.reps.get(m);
  A.cases.push(b);
  for(const j of A.st)big.add(pm(b.ids,gs[j]));
 }
 for(const m of big)A.pairs.add(m);
 edgeResults.push([A.t,B.t,n0,big.size,nOrb]);
}
if(types.map(x=>x.reps.size).join()!=='432,8640,6480,25920,2160,2160'||edgeResults.map(x=>x[4]).join()!=='4,13,2,21,4,4,51,5,1')throw Error('edge orbit census');
console.log({group:gs.length,masks:types.map(x=>x.reps.size),edges:edgeResults});

const pc=m=>{let n=0;for(;m;m&=m-1n)n++;return n;};
const inside=(u,v)=>(u&v)===u;
const comp=(a,b)=>inside(a.m,b.m)||inside(b.m,a.m);
const match=(a,b)=>{
 if(a.k>b.k)[a,b]=[b,a];
 if(types[a.k].ids.length+types[b.k].ids.length>12)return false;
 return types[a.k].pairs.has(pm(b.ids,gis[a.j]));
};
const answers=[], chist={};let fullCount=0, rawCount=0;
for(const T of types)for(const B of T.cases){
 const A=all.get(T.m), pre=A.m|B.m, pn=A.n|B.n, seed=pc(pre), gap=12-seed,Cs=[];
 for(const C of all.values()){
  if((C.m&pn)||comp(C,A)||comp(C,B))continue;
  if(pc(C.m&~pre)>gap)continue;
  Cs.push(C);
 }
 let n2=0, sig={},w=null;
 for(let i=0;i<Cs.length;i++)for(let j=0;j<i;j++){
  const C=Cs[i],D=Cs[j];if(C.m&(D.m|D.n)||pc((C.m|D.m)&~pre)>gap)continue;
  if(!match(C,D))continue;n2++;rawCount++;
  sig[[C.k,D.k].sort().join(',')]=(sig[[C.k,D.k].sort().join(',')]||0)+1;
  if(!w)w=[A.ids,B.ids,C.ids,D.ids];
 }
 if(n2){fullCount++;const k=[T.t,B.k].join();chist[k]=(chist[k]??0)+1;answers.push({type:[T.t,B.k],n2,sig,nc:Cs.length,w});}
}
if(fullCount!==2||rawCount!==2||!answers.every(x=>x.type.join()==='1,1'&&x.n2===1&&x.sig['1,1']===1))throw Error('disjoint edge census');
console.log({fourMaskPatterns:rawCount,bothEdgesOfTypes:'6a+6a'});

function excludeCross(a,b){
 if(pc(a.m&b.m)!==5)throw Error('expected five common blockers');
 const AA=types[a.k],BB=types[b.k], inv=gis[a.j], normalized=pm(b.ids,inv),models=new Set();
 for(const j of AA.st)models.add(pm(BB.reps.get(normalized).ids,gs[j]));
 let lo=Infinity,eq=0, checked=0;
 for(let j=0;j<gs.length;j++){
  if(!models.has(pm(BB.ids,gs[j])))continue;
  const inv=gis[j];
  for(const [ib,v] of BB.h.entries()){
   const y=Array.from(inv.slice(0,6),i=>dd(rr[i],v));
   for(const [ia,da] of AA.dh.entries()){
    const n=dd(da,y);if(n < -cutoff)throw Error('cross pair not excluded');
    if(n===-cutoff){
      if(![AA.h[ia],v].every(w=>w[5]>0&&w.slice(0,5).every(x=>x===0)))throw Error('nonroot equality');
      eq++;
    }
    lo=Math.min(lo,n);checked++;
   }
  }
 }
 if(lo!==-cutoff||!eq||!checked)throw Error('cross orbit');
 return [checked,eq];
}
let final=[];
for(const {w} of answers){
 const [A,B,C,D]=w.map(ids=>all.get(mask(ids)));
 final.push([excludeCross(A,D),excludeCross(B,C)]);
}
console.log({crossChecks:final});
