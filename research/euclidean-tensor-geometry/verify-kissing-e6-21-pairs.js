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

const nxt9=new Map();for(const set of n8.values())for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){const t=set.concat([positive.indexOf(r)]).sort((a,b)=>a-b);nxt9.set(t.join(),t);}
const groups9=[...nxt9.values()].map(ids=>ids.map(i=>positive[i]));

const nxt10=new Map();for(const set of nxt9.values())for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){const t=set.concat([positive.indexOf(r)]).sort((a,b)=>a-b);nxt10.set(t.join(),t);}
const groups10=[...nxt10.values()].map(ids=>ids.map(i=>positive[i]));
const tenRep=[];for(const C of groups10){if(!tenRep.some(D=>lab(D)===lab(C)||lab(D.map(reverse))===lab(C)))tenRep.push(C);}
const f5=groups5.find(C=>C.every(r=>r[1]===2n)), V5=E[0].map(v=>12n*v);
const L=1152, detG=Number(determinant);
const h5=vertices(f5).filter(w=>w.join()!==V5.join()).flatMap(w=>[w.map(v=>96n*v),w.map((v,i)=>48n*(v+V5[i]))]);
const types=[f5,groups6[0],groups6[1],groups[0],groups[1],groups[2],...groups8.slice(0,4),...groups9.slice(0,4),...tenRep].map((C,t)=>{
 const vs=vertices(C),h=t===0?h5:sliceHull(vs).map(w=>vs.some(v=>norm(v)>N0)?w:w.map(x=>96n*x));
 return {C,ids:getMask(C),m:mask(getMask(C)),h:h.map(x=>x.map(Number)),t,reps:new Map(), st:[], pairs:new Set(), cases:[]};
});
if(groups.length!==4||groups6.length!==3||lab(groups[0].map(reverse))!==lab(groups[3])||lab(groups6[0].map(reverse))!==lab(groups6[2]))throw Error('lower chamber coverage');
if(groups5.filter(isStar).length!==2||lab(groups5.filter(isStar)[0].map(reverse))!==lab(groups5.filter(isStar)[1]))throw Error('five-mask coverage');
if(groups9.map(C=>groups9.findIndex(B=>lab(B)===lab(C.map(reverse)))).join()!=='5,6,2,4,3,0,1')throw Error('nine diagram coverage');
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
 if(B.t<A.t||A.ids.length+B.ids.length>15)continue;
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
if(types.map(x=>x.reps.size).join()!=='432,8640,6480,25920,2160,2160,17280,4320,25920,270,4320,25920,25920,12960,12960,8640,8640,51840,6480')throw Error('mask count');
console.log({group:gs.length,masks:types.map(x=>x.reps.size),edges:edgeResults});

for(const a of types) {
 a.cCache=new Map();
 a.root=a.h.map(w=>w[5]>0&&w.slice(0,5).every(x=>x===0));
 a.ns=a.h.map((w,i)=>dd(a.dh[i],w));
}
const maxN=Math.max(...types.flatMap(t=>t.ns));if(4*maxN*maxN>=2**52)throw Error('binary64 squared comparison');let newCalls=0,allCalls=0;
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
 if(types[a.k].ids.length+types[b.k].ids.length>15)return false;
 return types[a.k].pairs.has(pm(b.ids,gis[a.j]));
};
const goodFours=[],answers=[], chist={};let fullCount=0, rawCount=0;
let nCase=0;for(const T of types)for(const B of T.cases){
 nCase++;
 const A=all.get(T.m), pre=A.m|B.m, pn=A.n|B.n, seed=pc(pre), gap=15-seed,Cs=[];
 for(const C of all.values()){
  if((C.m&pn)||comp(C,A)||comp(C,B))continue;
  const extra=pc(C.m&~pre);if(extra>gap)continue;
  Cs.push([extra,C]);
 }
 Cs.sort((a,b)=>a[0]-b[0]);let n2=0, sig={},w=null;
 for(let i=0;i<Cs.length;i++)for(let j=0;j<i;j++){
  if(Cs[i][0]+Cs[j][0]>gap)break;
  const C=Cs[i][1],D=Cs[j][1];if(C.m&(D.m|D.n))continue;
  if(!match(C,D))continue;rawCount++;if(incompatible(A,C)||incompatible(A,D)||incompatible(B,C)||incompatible(B,D))continue;n2++;
  sig[[C.k,D.k].sort().join(',')]=(sig[[C.k,D.k].sort().join(',')]||0)+1;
  const ww=[A.ids,B.ids,C.ids,D.ids];goodFours.push(ww);if(!w)w=ww;
 }
 if(n2){fullCount++;const k=[T.t,B.k].join();chist[k]=(chist[k]??0)+1;answers.push({type:[T.t,B.k],n2,sig,nc:Cs.length,w});}
}
if(nCase!==1160||rawCount!==412423||goodFours.length!==35354)throw Error('matching census');console.log({anchorOrbits:nCase,rawCount,afterPositive:goodFours.length});

for(const a of types)a.eCA=new Map();
function edgeForm(a,b){
 const gi=gis[a.j],mid=pm(b.ids,gi),T=types[a.k],B=types[b.k];
 let entry=T.eCA.get(mid);
 if(!entry){const ids=B.reps.get(mid).ids;let min=null,stab=[];for(const j of T.st){let z=pm(ids,gs[j]);if(min===null||z<min){min=z;stab=[j];}else if(z===min)stab.push(j);}
  entry=[min,stab];T.eCA.set(mid,entry);}
 return {tk:a.k,gi,min:entry[0],sel:entry[1]};
}
function canonKey(ww){
 const [a,b,c,d]=ww.map(ids=>all.get(mask(ids)));
 const ordered=[[a,b,c,d],[b,a,c,d],[c,d,a,b],[d,c,a,b]],tmin=Math.min(a.k,b.k,c.k,d.k),possible=[];
 let mk=null;
 for(const [a,b,c,d] of ordered){if(a.k!==tmin)continue;const e=edgeForm(a,b);if(mk===null||e.min<mk){mk=e.min;possible.length=0;}if(e.min===mk)possible.push([e,c.ids,d.ids]);}
 let minC=null,minD=null;
 for(const [{gi,sel},cs,ds] of possible){const C=cs.map(i=>gi[i]),D=ds.map(i=>gi[i]);for(const k of sel){let c=pm(C,gs[k]),d=pm(D,gs[k]);if(c>d)[c,d]=[d,c];if(minC===null||c<minC||c===minC&&d<minD){minC=c;minD=d;}}}
 return [tmin,mk,minC,minD].join(',');
}
const forms=new Map();for(const w of goodFours){const key=canonKey(w);if(!forms.has(key))forms.set(key,w);}
const fourlist=[...forms.values()];
const fours=fourlist;if(fours.length!==5377)throw Error('canonical class count');

const fork=groups5.find(C=>!isStar(C)),forkIds=getMask(fork),forkSet=new Set(gs.map(p=>pm(forkIds,p)));
let step=[...nxt10.values()];const domMask=[];
for(let k=11;k<=15;k++){const next=new Map();for(const set of step)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
 const t=set.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(t.join(),t);
}step=[...next.values()];domMask[k]=new Set(step.map(ids=>mask(ids.map(i=>index.get(positive[i].join())))));}
const highMem=new Map(),ums=new Map(),etc=rr.map(v=>v.map(Number)),gramR=G.map(v=>v.map(Number));
function highYes(x){
 if(highMem.has(x.m))return highMem.get(x.m);
 let y=x.ids,s=I.map(k=>y.reduce((a,i)=>a+rr[i][k],0));let depth=0;
 while(true){
  let k=I.find(i=>dd(gramR[i],s)<0);if(k===undefined)break;
  s[k]-=dd(gramR[k],s); y=y.map(v=>permutations[k][v]);if(++depth>40)throw Error('not dominant');
 }
 const ok=domMask[y.length].has(mask(y));highMem.set(x.m,ok);return ok;
}
function allInU(ids){
 const u=mask(ids);if(ums.has(u))return ums.get(u);
 const cand=[],h=[],seed=[];
 for(let i=0;i<11;i++)for(let j=i+1;j<12;j++)for(let k=j+1;k<13;k++)for(let l=k+1;l<14;l++)for(let m=l+1;m<15;m++){
  const z=[ids[i],ids[j],ids[k],ids[l],ids[m]],mm=mask(z),v=all.get(mm);
  if(v){cand.push(v);seed.push(v);}else if(forkSet.has(mm))seed.push({m:mm,ids:z});
 }
 let prev=seed;
 for(let n=6;n<=15;n++){
  const sets=new Map();
  for(const c of prev)for(const d of ids){
   const m=c.m|bit[d];if(m===c.m||sets.has(m))continue;
   if(n<=10){if(all.has(m))sets.set(m,all.get(m));}
   else{const v={m,ids:c.ids.concat([d])};if(highYes(v))sets.set(m,v);}
  }
  if(!sets.size)break;prev=[...sets.values()];if(n<=10)cand.push(...prev);else h.push(...prev);
 }
 const z={cand,h};ums.set(u,z);return z;
}
const cliqueAtLeast=(V,n)=>{
 if(n<=0)return true;if(V.length<n)return false;
 for(let i=0;i<=V.length-n;i++)if(cliqueAtLeast(V.slice(i+1).filter(y=>!incompatible(V[i],y)),n-1))return true;
 return false;
};
let early=0,anchor=0,cliq=0,remaining=[],total=0,nhigh=0;
for(const [ci,ww] of fours.entries()){
 const ff=ww.map(x=>all.get(mask(x))), base=[...new Set(ww.flat())];const rest=Array.from({length:72},(_,i)=>i).filter(i=>!base.includes(i)&&!base.includes(negative[i]));const uu=[];
 if(base.length===15)uu.push(base);
 else if(base.length===14){for(const i of rest)uu.push(base.concat([i]));}
 else if(base.length===13){for(const [k,i] of rest.entries())for(const j of rest.slice(k+1))if(negative[i]!==j)uu.push(base.concat([i,j]));}
 else throw Error('bad size');
 for(const u of uu){
  total++;const {cand,h}=allInU(u);if(h.length)nhigh++;
  if(cand.length+h.length<16){early++;continue;}
  const opt=cand.filter(z=>!ff.includes(z)&&ff.every(y=>!incompatible(z,y)));
  if(opt.length+h.length<12){anchor++;continue;}
  if(!cliqueAtLeast(opt,12-h.length)){cliq++;continue;}
  remaining.push([ci,u,opt.map(o=>o.ids),h.map(o=>o.ids)]);
 }
 
}
console.log({cases:fours.length,completed:total,distinct:ums.size,early,anchor,cliq,nhigh,rem:remaining.length});
if(total!==27010||early!==2158||anchor!==23690||cliq!==1162||remaining.length!==0)throw Error('final outsider census');
