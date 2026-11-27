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
const bil=(a,b)=>dot(a,adj.map(row=>dot(row,b)));
function test(C){
 const inds=C.map((_,i)=>i), N=C.length;
 const subsets=(A,k)=>k===0?[[]]:A.flatMap((a,i)=>subsets(A.slice(i+1),k-1).map(r=>[a,...r]));
 let B=subsets(inds,6).find(ids=>det(ids.map(i=>C[i])));if(!B)B=subsets(inds,5).find(ids=>I.some(j=>det(ids.map(i=>C[i]).concat([E[j]]))));
 if(!B)throw Error('rank below 5');
 const H=sliceHull(vertices(C));
 const M=C.map(r=>C.map(s=>gram(r,s)));
 const basis=B.map(i=>C[i]);
 let n=null;
 if(B.length===5){
    const Gbasis=basis.map(r=>G.map(row=>dot(row,r)));
    n=I.map(i=>BigInt(i%2?-1:1)*det(Gbasis.map(row=>row.filter((_,j)=>i!==j))));
    if(n.every(v=>!v))throw Error("orthogonal");
 }
 let checked=0, bad=0, eq=0,badPairs=[];
 for(const p of permutationsSmall(inds)){
  if(inds.some(i=>inds.some(j=>M[i][j]!==M[p[i]][p[j]])))continue;
  for(const sign of n?[1n,-1n]:[1n]){
   const matrix=n?basis.concat([n]):basis;
   for(let i=0;i<H.length;i++){
    const q=H[i], vals=B.map(i=>dot(C[p[i]],q));
    if(n)vals.push(sign*dot(n,q));
    const {y,d}=solve(matrix,vals);
    if(norm(y)!==d*d*norm(q))throw Error("not isometry");
    for(let j=0;j<H.length;j++){
     checked++;const a=H[j], u=bil(a,y),gap=4n*u*u-norm(a)*norm(y);
     if(u<=0n||gap<0n){bad++;if(badPairs.length<10)badPairs.push([i,j,Number(u)/Math.sqrt(Number(norm(a)*norm(y)))]);}
     if(gap===0n&&u>0n){eq++;badPairs.push([i,j,'eq']);}
    }
   }
  }
 }
 return {checked,bad,eq,badPairs,hull:H.map(v=>v.join())};
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



let ideals8=[...ideals];const n8=new Map();
for(const set of ideals8)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
 const t=[...set,positive.indexOf(r)].sort((a,b)=>a-b);n8.set(t.join(),t);
}
const groups8=[...n8.values()].map(ids=>ids.map(i=>positive[i]));
if(lab(groups8[0].map(reverse))!==lab(groups8[4])||lab(groups8[1].map(reverse))!==lab(groups8[5]))throw Error('8 diagram');
const f5=groups5.find(C=>C.every(r=>r[1]===2n)), V5=E[0].map(v=>12n*v);
const L=1152, detG=Number(determinant);
const h5=vertices(f5).filter(w=>w.join()!==V5.join()).flatMap(w=>[w.map(v=>96n*v),w.map((v,i)=>48n*(v+V5[i]))]);
const types=[f5,groups6[0],groups6[1],groups[0],groups[1],groups[2],...groups8.slice(0,4)].map((C,t)=>{
 const vs=vertices(C),h=t===0?h5:sliceHull(vs).map(w=>vs.some(v=>norm(v)>N0)?w:w.map(x=>96n*x));
 return {C,ids:getMask(C),m:mask(getMask(C)),h:h.map(x=>x.map(Number)),t,reps:new Map(), st:[], pairs:new Set(), cases:[]};
});
if(groups.length!==4||groups6.length!==3||lab(groups[0].map(reverse))!==lab(groups[3])||lab(groups6[0].map(reverse))!==lab(groups6[2]))throw Error('lower chamber coverage');
if(groups5.filter(isStar).length!==2||lab(groups5.filter(isStar)[0].map(reverse))!==lab(groups5.filter(isStar)[1]))throw Error('five-mask coverage');
const z8=groups8.map(test);
if(z8.some(q=>q.bad||q.badPairs.some(([i,j])=>[i,j].some(k=>q.hull[k].split(',').some((x,r)=>r!==5&&x!=='0')))))throw Error('eight-blocker nonroot equality');
if(z8.map(q=>q.checked).join()!=='600,2400,400,92928,600,2400')throw Error('8-capacity count');
console.log({eightMaskCapacity:z8.map(q=>[q.checked,q.eq])});
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
   X.ts=[];A.reps.set(mA,X);all.set(mA,X);
  }
  A.reps.get(mA).ts.push(j);if(mA===A.m)A.st.push(j);
 }
}
const rr=roots.map(r=>r.map(Number)),adjN=adj.map(r=>r.map(Number));
const dd=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3]+a[4]*b[4]+a[5]*b[5];
const maxAbs=xs=>Math.max(...xs.flat(Infinity).map(Math.abs));
const mxR=maxAbs(rr),mxH=maxAbs(types.flatMap(t=>t.h)),mxAdj=maxAbs(adjN);
if(36*mxR*mxH*6*mxAdj*mxH>=2**52||!types.every(t=>t.h.every(h=>h.every(Number.isSafeInteger))))throw Error('binary64 dot comparison');
for(const A of types)A.dh=A.h.map(a=>adjN.map(r=>dd(r,a)));
const cutoff=-(L**2)*detG;
let edgeResults=[];
for(const A of types)for(const B of types){
 if(B.t<A.t||A.ids.length+B.ids.length>13)continue;
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
if(types.map(x=>x.reps.size).join()!=='432,8640,6480,25920,2160,2160,17280,4320,25920,270')throw Error('mask count');
if(edgeResults.reduce((a,b)=>a+b[4],0)!==[4,13,2,21,4,4,16,9,15,2,51,5,81,9,12,1,7,0,2].reduce((a,b)=>a+b,0))throw Error('edge count');
console.log({group:gs.length,masks:types.map(x=>x.reps.size),edges:edgeResults});

for(const a of types) {
 a.cCache=new Map();
 a.root=a.h.map(w=>w[5]>0&&w.slice(0,5).every(x=>x===0));
 a.ns=a.h.map((w,i)=>dd(a.dh[i],w));
}
const maxN=Math.max(...types.flatMap(t=>t.ns));
if(4*maxN*maxN>=2**52)throw Error('binary64 squared comparison'); // Cauchy-Schwarz and exact isometries bound |u| by maxN.
let newCalls=0,allCalls=0;
function incompatible(a,b){
 allCalls++;
 if(a.k>b.k)[a,b]=[b,a];
 const aa=types[a.k], bb=types[b.k], b0=bb.reps.get(pm(b.ids,gis[a.j]));
 if(aa.cCache.has(b0.m))return aa.cCache.get(b0.m);
 const orb=new Set();for(const k of aa.st)orb.add(pm(b0.ids,gs[k]));
 newCalls++;
 let exclude=true;
 outer:for(const m of orb)for(const k of bb.reps.get(m).ts){
  const inv=gis[k], y=bb.h.map(v=>[dd(rr[inv[0]],v),dd(rr[inv[1]],v),dd(rr[inv[2]],v),dd(rr[inv[3]],v),dd(rr[inv[4]],v),dd(rr[inv[5]],v)]);
  const vals=aa.dh.map(a=>y.map(v=>dd(a,v))), TH=-cutoff;
  const lin=vals.every((row,i)=>row.every((u,j)=>u>TH||u===TH&&(aa.root[i]||bb.root[j])));
  if(lin)continue;
  const rowwise=(T,A,B)=>T.every((row,i)=>{
      const count=(j,z)=>z>0||z===0&&(A.root[i]||B.root[j]);
      return row.every((u,j)=>u>=0&&count(j,2*u*u-A.ns[i]*TH)) ||
             row.every((u,j)=>u>=0&&count(j,4*u*u-A.ns[i]*B.ns[j]));
  });
  if(rowwise(vals,aa,bb)||rowwise(bb.h.map((_,j)=>vals.map(row=>row[j])),bb,aa))continue;
  exclude=false;break outer;
 }
 for(const x of orb)aa.cCache.set(x,exclude);
 return exclude;
}

const pc=m=>{let n=0;for(;m;m&=m-1n)n++;return n;};
const inside=(u,v)=>(u&v)===u;
const comp=(a,b)=>a.m===b.m||(a.ids.length<8&&b.ids.length<8&&(inside(a.m,b.m)||inside(b.m,a.m)));
const match=(a,b)=>{
 if(a.k>b.k)[a,b]=[b,a];
 if(types[a.k].ids.length+types[b.k].ids.length>13)return false;
 return types[a.k].pairs.has(pm(b.ids,gis[a.j]));
};
const goodFours=[],answers=[], chist={};let fullCount=0, rawCount=0;
for(const T of types)for(const B of T.cases){
 const A=all.get(T.m), pre=A.m|B.m, pn=A.n|B.n, seed=pc(pre), gap=13-seed,Cs=[];
 for(const C of all.values()){
  if((C.m&pn)||comp(C,A)||comp(C,B))continue;
  if(pc(C.m&~pre)>gap)continue;
  Cs.push(C);
 }
 let n2=0, sig={},w=null;
 for(let i=0;i<Cs.length;i++)for(let j=0;j<i;j++){
  const C=Cs[i],D=Cs[j];if(C.m&(D.m|D.n)||pc((C.m|D.m)&~pre)>gap)continue;
  if(!match(C,D))continue;rawCount++;if(incompatible(A,C)||incompatible(A,D)||incompatible(B,C)||incompatible(B,D))continue;n2++;
  sig[[C.k,D.k].sort().join(',')]=(sig[[C.k,D.k].sort().join(',')]||0)+1;
  const ww=[A.ids,B.ids,C.ids,D.ids];goodFours.push(ww);if(!w)w=ww;
 }
 if(n2){fullCount++;const k=[T.t,B.k].join();chist[k]=(chist[k]??0)+1;answers.push({type:[T.t,B.k],n2,sig,nc:Cs.length,w});}
}
if(rawCount!==577||goodFours.length!==48)throw Error('matching count');console.log({matchingPatterns:rawCount,afterPositive:goodFours.length});

const forms=new Map();
for(const ww of goodFours){
 let best=null;
 for(const [a,b,c,d] of [[0,1,2,3],[0,1,3,2],[1,0,2,3],[1,0,3,2],[2,3,0,1],[2,3,1,0],[3,2,0,1],[3,2,1,0]]){
  const z=all.get(mask(ww[a]));
  for(const j of z.ts){const inv=gis[j];
   const key=[z.k,...[b,c,d].map(t=>pm(ww[t],inv).toString(16).padStart(18,"0"))].join("-");
   if(best===null||best>key)best=key;
  }
 }
 if(!forms.has(best))forms.set(best,[]);forms.get(best).push(ww);
}
console.log([...forms.values()].map(A=>[A.length,A[0].map(m=>m.length).join()]));
if(forms.size!==8)throw Error('matching classes');const canonical=[...forms.values()].map(C=>C[0]);

const Us=canonical.map(ww=>ww.flat().reduce((m,i)=>m|bit[i],0n));if(Us.some(m=>pc(m)!==13))throw Error('not forced full U');
let iAt9=new Map();
for(const set of n8.values())for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
 const t=set.concat([positive.indexOf(r)]).sort((a,b)=>a-b);iAt9.set(t.join(),t);
}
if(iAt9.size!==7)throw Error('nine ideal count');
for(const set of iAt9.values()){
 const ids=set.map(i=>index.get(positive[i].join()));
 for(const perm of gs){const m=pm(ids,perm);if(Us.some(u=>(m&u)===m))throw Error('possible nine-blocker ideal');}
}
// Any upward ideal with more than nine roots contains a nine-root upward ideal, so no larger mask fits either.
const cap=[];
for(const [i,U] of Us.entries()){
 const four=canonical[i].map(ids=>all.get(mask(ids)));
 const possible=[...all.values()].filter(z=>inside(z.m,U));
 if(possible.length===14){
   if([5,6,7,8].map(n=>possible.filter(z=>z.ids.length===n).length).join()!=='4,8,2,0')throw Error('unexpected size profile');
   if(!possible.some(x=>possible.some(y=>x.ids.length===6&&y.ids.length===7&&inside(x.m,y.m))))throw Error('no forbidden nested pair');
   cap.push(13);
 }else{
   if([5,6,7,8].map(n=>possible.filter(z=>z.ids.length===n).length).join()!=='4,22,13,2')throw Error('unexpected large union');
   const compat=possible.filter(z=>four.every(f=>z.m===f.m||!incompatible(z,f)));
   if(compat.length>=14)throw Error('14 outsider slots possible');
   cap.push(compat.length);
 }
}
if(cap.sort((a,b)=>a-b).join()!=='9,13,13,13,13,13,13,13')throw Error('unexpected cap');console.log({outsiderCapacityUpper:cap});
