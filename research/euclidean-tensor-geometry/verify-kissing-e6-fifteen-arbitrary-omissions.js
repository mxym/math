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
  
  const cap=I.filter(i=>!U.some(r=>r[i]>0n));const rows=[...E,...U,...L,...cap.map(i=>E[i])], rhs=[...I.map(()=>0n),...U.map(()=>1n),...L.map(()=>1n),...cap.map(()=>2n)], out=new Map();
  function visit(set,start){
    if(set.length<6){
      for(let i=start;i<=rows.length-6+set.length;i++)visit([...set,i],i+1);
      return;
    }
    const a=set.map(i=>rows[i]),b=set.map(i=>rhs[i]);
    let d=det(a);if(!d)return;
    const N=I.map(j=>det(a.map((r,i)=>r.map((v,k)=>j===k?b[i]:v))));
    if(d<0n){d=-d;N.forEach((v,i)=>N[i]=-v);}
    if(N.some(v=>v<0n)||cap.some(i=>N[i]>2n*d)||U.some(r=>dot(r,N)>d)||L.some(r=>dot(r,N)<d))return;
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
const nxt11=new Map();for(const set of nxt10.values())for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){const t=set.concat([positive.indexOf(r)]).sort((a,b)=>a-b);nxt11.set(t.join(),t);}
const groups11=[...nxt11.values()].map(ids=>ids.map(i=>positive[i]));
const elevenRep=[];for(const C of groups11){if(!elevenRep.some(D=>lab(D)===lab(C)||lab(D.map(reverse))===lab(C)))elevenRep.push(C);}
const f5=groups5.find(C=>C.every(r=>r[1]===2n)), V5=E[0].map(v=>12n*v);
const L=1152, detG=Number(determinant);
const h5=sliceHull(vertices(f5));
const types=[f5,groups6[0],groups6[1],groups[0],groups[1],groups[2],...groups8.slice(0,4),...groups9.slice(0,4),...tenRep,...elevenRep].map((C,t)=>{
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
const rr=roots.map(r=>r.map(Number)),adjN=adj.map(r=>r.map(Number));
const dd=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3]+a[4]*b[4]+a[5]*b[5];
const maxAbs=xs=>Math.max(...xs.flat(Infinity).map(Math.abs));
const mxR=maxAbs(rr),mxH=maxAbs(types.flatMap(t=>t.h)),mxAdj=maxAbs(adjN);
if(36*mxR*mxH*6*mxAdj*mxH>=2**52||!types.every(t=>t.h.every(h=>h.every(Number.isSafeInteger))))throw Error('binary64 dot comparison');
const cutoff=-(L**2)*detG;
function cmp(f,u,a,b){if(Math.max(Math.abs(u),a,b)<=30000000)return f*u*u-a*b;const d=BigInt(f)*BigInt(u)*BigInt(u)-BigInt(a)*BigInt(b);return d<0n?-1:d===0n?0:1;}const gn=G.map(r=>r.map(Number)),giMap=new Map(gs.map((p,i)=>[gkey(p),i]));
const left=permutations.map(q=>Uint32Array.from(gs,p=>giMap.get(gkey([q[p[0]],q[p[1]],q[p[2]],q[p[3]],q[p[4]],q[p[5]]]))));
const types0=types;
{
const invIdx=gis.map(p=>giMap.get(gkey(p)));
function compose(i,j){const p=gs[i],q=gs[j];return giMap.get(gkey([p[q[0]],p[q[1]],p[q[2]],p[q[3]],p[q[4]],p[q[5]]]));}
const types=types0.slice(),fork=groups5.find(C=>!isStar(C));
function addType(C){const t=types.length;
 const vs=vertices(C),h=sliceHull(vs).map(w=>vs.some(v=>norm(v)>N0)?w:w.map(x=>96n*x));
 types.push({C,ids:getMask(C),m:mask(getMask(C)),h:h.map(x=>x.map(Number)),t});
}
addType(fork);let step=[...nxt11.values()];
for(let k=12;k<=16;k++){const next=new Map();for(const set of step)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
 const t=set.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(t.join(),t);
}step=[...next.values()];const cs=[];for(const ids of step){const C=ids.map(i=>positive[i]);if(!cs.some(x=>lab(x)===lab(C)||lab(x.map(reverse))===lab(C))){cs.push(C);addType(C);}}}
const ix=new Map();
for(const T of types){const m=T.m;ix.set(m,[T.t,0]);const rev=pm(T.ids,permutations[6]);if(rev!==m)ix.set(rev,[T.t,left[6][0]]);
 const s=I.map(k=>T.ids.reduce((a,i)=>a+rr[i][k],0)),stgen=I.filter(i=>dd(gn[i],s)===0);if(rev===m)stgen.push(6);
 const stab=[0],seen=new Set([0]);for(let j=0;j<stab.length;j++)for(const a of stgen){const h=left[a][stab[j]];if(!seen.has(h)){seen.add(h);stab.push(h);}}
 if(!stab.every(j=>pm(T.ids,gs[j])===m))throw Error('mask stabilizer');
 T.st=stab;T.dh=T.h.map(a=>adjN.map(v=>dd(v,a)));T.root=T.h.map(w=>w[5]>0&&w.slice(0,5).every(x=>x===0));T.ns=T.h.map((w,i)=>dd(T.dh[i],w));T.cCache=new Map();
}
const mxH2=maxAbs(types.flatMap(t=>t.h));if(36*mxR*mxH2*6*mxAdj*mxH2>=2**52||!types.every(t=>t.h.every(h=>h.every(Number.isSafeInteger))))throw Error('binary64 high dots');
function recognize(ids){
 const s=I.map(k=>ids.reduce((a,i)=>a+rr[i][k],0));let j=0,steps=0;
 for(;;){const i=I.find(i=>dd(gn[i],s)<0);if(i===undefined)break;s[i]-=dd(gn[i],s);j=left[i][j];if(++steps>36)throw Error('Weyl reduction');}
 const hit=ix.get(pm(ids,gs[j]));if(!hit)return null;
 const [k,jj]=hit,transport=compose(invIdx[j],jj);if(pm(types[k].ids,gs[transport])!==mask(ids))throw Error('bad transporter');
 return [k,transport];
}
for(const T of types){T.ch=[];if(T.ids.length>=16)continue;
 for(let i=0;i<72;i++){if(T.ids.includes(i)||T.ids.includes(negative[i]))continue;const hit=recognize(T.ids.concat([i]));if(hit)T.ch.push([i,hit[0],hit[1]]);}
}
const seedTypes=[types[0],types[25]];if(!seedTypes.every(t=>t.ids.length===5))throw Error('seed indices');
const seeds=new Map();for(const T of seedTypes){const tot=103680/T.st.length;for(let j=0;j<gs.length;j++){const m=pm(T.ids,gs[j]);if(!seeds.has(m))seeds.set(m,{k:T.t,j,m});}if([...seeds.values()].filter(v=>v.k===T.t).length!==tot)throw Error('five orbit');}
function opts(ids){
 const U=mask(ids),cand=[],seen=new Map();for(const [m,t] of seeds)if((m&U)===m)seen.set(m,t);
 for(const [m,t] of seen){if(t.k!==25)cand.push(t);for(const [i,k,l] of types[t.k].ch){const b=bit[gs[t.j][i]];if(!(b&U))continue;const mm=m|b;if(!seen.has(mm))seen.set(mm,{k,j:compose(t.j,l),m:mm});}}
 return cand;
}

function incompatibleBase(a,b){
 if(a.k>b.k)[a,b]=[b,a];const aa=types[a.k],bb=types[b.k],rel=compose(invIdx[a.j],b.j), m0=pm(bb.ids,gs[rel]);if(aa.cCache.has(m0))return aa.cCache.get(m0);
 const orb=new Map();for(const p of aa.st){const j=compose(p,rel),m=pm(bb.ids,gs[j]);if(!orb.has(m))orb.set(m,j);}
 let exclude=true;
 outer:for(const i of orb.values())for(const j of bb.st){const k=compose(i,j);
  const inv=gis[k], y=bb.h.map(v=>[dd(rr[inv[0]],v),dd(rr[inv[1]],v),dd(rr[inv[2]],v),dd(rr[inv[3]],v),dd(rr[inv[4]],v),dd(rr[inv[5]],v)]);
  const vals=aa.dh.map(a=>y.map(v=>dd(a,v))), TH=-cutoff;
  const lin=vals.every((row,i)=>row.every((u,j)=>u>TH||u===TH&&(aa.root[i]||bb.root[j])));
  if(lin)continue;
  const rowwise=(T,A,B)=>T.every((row,i)=>{
      const count=(j,z)=>z>0||z===0&&(A.root[i]||B.root[j]);
      return row.every((u,j)=>u>=0&&count(j,cmp(2,u,A.ns[i],TH))) ||
             row.every((u,j)=>u>=0&&count(j,cmp(4,u,A.ns[i],B.ns[j])));
  });
  if(rowwise(vals,aa,bb)||rowwise(bb.h.map((_,j)=>vals.map(row=>row[j])),bb,aa))continue;
  exclude=false;break outer;
 }for(const m of orb.keys())aa.cCache.set(m,exclude);return exclude;
}

const smallCache=types.map(()=>[]);function incompatible(a,b){if(a.k>b.k)[a,b]=[b,a];const rel=compose(invIdx[a.j],b.j);let cmap=smallCache[a.k][b.k];if(!cmap)smallCache[a.k][b.k]=cmap=new Uint8Array(gs.length);const z=cmap[rel];if(z)return z===2;const out=incompatibleBase(a,b);cmap[rel]=out?2:1;return out;}
function clique(V,n){
 if(n<=0)return true;if(V.length<n)return false;
 const colors=[];for(const a of V){const c=colors.find(c=>c.every(b=>incompatible(a,b)));if(c)c.push(a);else colors.push([a]);}
 if(colors.length<n)return false;
 for(let c=colors.length-1;c>=n-1;c--){const prev=colors.slice(0,c).flat();for(const a of colors[c])if(clique(prev.filter(b=>!incompatible(a,b)),n-1))return true;}
 return false;
}

function viable(T){
const P=T.C.filter(r=>!T.C.some(s=>s!==r&&s.every((x,i)=>x<=r[i]))),A=[...E,...P],b=A.map((r,i)=>BigInt(i>=6)),Q=A.map(r=>A.map(s=>dot(r,G.map(row=>dot(row,s)))));let ret=true;
 function go(J,i){if(!ret)return;if(J.length){const K=J.map(i=>J.map(j=>Q[i][j])),D=det(K);if(D>0n){const v=J.map(i=>b[i]),z=v.map((_,i)=>det(K.map((r,j)=>r.map((x,k)=>k===i?v[j]:x))));if(z.every(x=>x>=0n)&&dot(z,v)>=2n*D){ret=false;return;}}}if(J.length<6)for(let j=i;j<A.length;j++)go(J.concat([j]),j+1);}
 go([],0);return ret;
}
for(const t of types)t.via=viable(t);console.log('infeasible types',types.filter(t=>!t.via).map(t=>[t.t,t.ids.length,t.h.length]));


const RG=rr.map(v=>{const a=gn.map(row=>dd(row,v));return rr.map(w=>dd(a,w));});
const masks=RG.map(row=>[0,1].map(u=>row.reduce((s,t,i)=>t===u?s|bit[i]:s,0n)));
const pc=x=>{let n=0;while(x){n++;x&=x-1n;}return n;};
const cap=16,bag=Array.from({length:72},()=>[]),refs=[];
for(const T of types){if(!T.via||T.t===25||!T.h.length)continue;const valid=T.ids.filter(r=>2*pc(T.m&masks[r][1])+pc(T.m&masks[r][0])<=cap);
 if(!valid.length)continue;for(const r of valid)refs.push([T,r]);const hit=new Set();for(let j=0;j<gs.length;j++){const g=gs[j],m=pm(T.ids,g);if(hit.has(m))continue;hit.add(m);for(const k of valid){const r=g[k];bag[r].push({k:T.t,j,m,a:m&masks[r][1],o:m&masks[r][0]});}}}

const stab0=gs.filter(g=>g[0]===0),transport=rr.map((r,i)=>gs.find(p=>p[i]===0)),idx2=Array.from({length:72},(_,i)=>i);
const ids=m=>idx2.filter(i=>m&bit[i]),orbP=new Map(),reps=[],NEG=[];
function insert(m,r){const mm=pm(ids(m),transport[r]);if(orbP.has(mm))return;const is=ids(mm),a=pc(mm&masks[0][1]),o=pc(mm&masks[0][0]),w=2*a+o,k=reps.length;
 for(const g of stab0){const m=pm(is,g);if(!orbP.has(m)){orbP.set(m,k);const n=pneg(is,g);NEG.push({n,a,o,w,pp:n&masks[0][0]});}}
 reps.push({mm,is,a,o,w,pp:mm&masks[0][0]});}
const hist={};for(const [T,r] of refs){const a=T.m&masks[r][1],o=T.m&masks[r][0];for(const v of bag[r]){if(v.m===T.m)continue;const ac=pc(a|v.a),op=pc(o|v.o),w=2*ac+op;if(w>cap)continue;if(incompatible({k:T.t,j:0},v))continue;
 hist[w]=(hist[w]||0)+1;insert(T.m|v.m,r);}}
if(Object.keys(hist).some(w=>Number(w)<10)||!hist[10])throw Error('weight bound');console.log('rooted pair weight counts',hist,'orbits',reps.length,'rooted sets',NEG.length);
const d5=orbit(idx2.filter(i=>!rr[i][0])).map(mask);if(d5.length!==27)throw Error('D5 count');const a5=idx2.filter(i=>i<negative[i]).map(i=>masks[i][0]);if(a5.some(am=>pc(am)!==30))throw Error('A5 sections');const rx=idx2;for(let m=12;m<=15;m++){
 const covered=new Set(),maxU=[],doneM=new Set();let pairs=0,templates=0,total=0,raw=0,hall=0,graph=0,kept=[],maxCand=0;
 function check(K,is){if(doneM.has(K))return;doneM.add(K);total++;if(d5.some(z=>pc(z&K)<=2)||a5.some(z=>{const h=z&K,n=pc(h);if(n<2)return true;if(n>2)return false;const x=ids(h);return RG[x[0]][x[1]]<=0;})){raw++;return;}
  const V=opts(is).filter(v=>types[v.k].via&&v.k!==25&&types[v.k].h.length);maxCand=Math.max(V.length,maxCand);
  if(V.length<m+1){raw++;return;}if(is.some(r=>V.filter(v=>v.m&bit[r]).length<2)){hall++;return;}
  if(!clique(V,m+1)){graph++;return;}kept.push(K.toString());
 }
 const byW=Array.from({length:cap+1},(_,i)=>NEG.filter(B=>B.w===i));let ii=0;for(const A of reps){if(A.w>m-2)continue;const ss=stab0.filter(g=>pm(A.is,g)===A.mm),covB=new Set(),covU=new Set();ii++;
  for(let wt=A.w;wt<=Math.min(cap,2*(m-2)-A.w);wt++)for(const B of byW[wt]){const base=2+A.a+B.a+pc(A.pp|B.pp);if(base>m)continue;
   pairs++;if(covB.has(B.n))continue;const bn=ids(B.n);for(const g of ss)covB.add(pm(bn,g));const U=A.mm|B.n;if(covU.has(U))continue;covU.add(U);const is=ids(U);if(is.length!==base)throw Error('cost');templates++;
   const free=rx.filter(i=>!(U&bit[i]));function sub(K,I,j,n){if(!n){check(K,I);return;}for(let k=j;k<=free.length-n;k++)sub(K|bit[free[k]],I.concat([free[k]]),k+1,n-1);}
   sub(U,is,0,m-base);
  }
 }if(kept.length)throw Error('surviving M at '+m);console.log('omitted',m,{pairs,templates,total,raw,hall,graph,kept,maxCand});}
}
