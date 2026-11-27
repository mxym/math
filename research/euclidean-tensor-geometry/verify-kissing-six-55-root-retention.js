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

// A rational supporting plane separates the entire Minkowski sum of two chamber hulls
// from the Euclidean ball of squared radius tau. Floating point ONLY proposes a plane.
const whBound=6*mxAdj*8192;
if(12*whBound*Math.max(8192,6*mxR*mxH2)>2**52||!Number.isSafeInteger(6*L*L*detG))throw Error('exact plane bounds');
function distanceMin(A,B,tau,strict){
 if(!A.length||!B.length)return true;
 const nA=A.length,nB=B.length,avg=R=>I.map(i=>R.reduce((s,x)=>s+x[i],0)/R.length);
 let h=avg(A).map((v,i)=>v+avg(B)[i]);const T=tau*detG*L*L;
 for(let it=0;it<16;it++){
  const hh=adjN.map(r=>dd(r,h)),hn=dd(hh,h);
  if(hn<=T*(1+1e-12))return false;
  let a=A[0],b=B[0],lo=dd(hh,a),hi=dd(hh,b);for(let j=1;j<nA;j++){const v=dd(hh,A[j]);if(v<lo){lo=v;a=A[j];}}for(let j=1;j<nB;j++){const v=dd(hh,B[j]);if(v<hi){hi=v;b=B[j];}}
  if(lo+hi>0&&(lo+hi)**2>=T*hn*.9999){const sc=8192/Math.max(...h.map(Math.abs)),w=h.map(x=>Math.round(x*sc)),wh=adjN.map(r=>dd(r,w)),wn=dd(wh,w);
   let m=Infinity,q=Infinity;for(const x of A)m=Math.min(m,dd(wh,x));for(const x of B)q=Math.min(q,dd(wh,x));if(!Number.isSafeInteger(wn)||!Number.isSafeInteger(m)||!Number.isSafeInteger(q)||!Number.isSafeInteger(m+q))throw Error('separation arithmetic');
   const s=BigInt(m+q),dif=s*s-BigInt(T)*BigInt(wn);if(s>0n&&wn>0&&(strict?dif>0n:dif>=0n))return true;
  }
  const v=a.map((x,i)=>x+b[i]-h[i]),vn=dd(v,adjN.map(r=>dd(r,v)));if(vn<1e-7)return false;const step=Math.max(0,Math.min(1,(hn-lo-hi)/vn));if(step<1e-10)return false;h=h.map((x,i)=>x+step*v[i]);
 }return false;
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
  if(distanceMin(aa.h,y,6,true))continue;exclude=false;break outer;
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

// Canonical 19-axis subsets. First quotient by a D5-equator stabilizer (16 spin axes and 20 equatorial axes),
// then compare only D5 placements with maximum spin intersection. Every orbit has such a placement.
const baseAxes=Array.from({length:72},(_,i)=>i).filter(i=>i<negative[i]),sp=baseAxes.filter(i=>rr[i][0]),eq=baseAxes.filter(i=>!rr[i][0]),axis=sp.concat(eq),ar=new Int8Array(72);
axis.forEach((r,i)=>{ar[r]=i;ar[negative[r]]=i;});if(sp.length!==16||eq.length!==20)throw Error('split');
const K=16;const perms=[],h=[],sections=new Map(),gstats=new Map();let burn=0;
const pop=x=>{x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return ((x+(x>>>4)&0x0f0f0f0f)*0x01010101)>>>24;};
class Lut{constructor(P){this.S=[];this.D=[];for(let i=0;i<5;i++){let n=1<<Math.min(8,36-8*i),s=new Int32Array(n),d=new Int32Array(n);for(let k=1;k<n;k++){const b=k&-k,j=P[8*i+31-Math.clz32(b)],r=k^b;s[k]=s[r]|(j<16?1<<j:0);d[k]=d[r]|(j>=16?1<<(j-16):0);}this.S.push(s);this.D.push(d);}}
 s(a,b){const t=this.S;return t[0][a&255]|t[1][a>>>8]|t[2][b&255]|t[3][b>>>8&255]|t[4][b>>>16];}
 d(a,b){const t=this.D;return t[0][a&255]|t[1][a>>>8]|t[2][b&255]|t[3][b>>>8&255]|t[4][b>>>16];}
 de(b){const t=this.D;return t[2][b&255]|t[3][b>>>8&255]|t[4][b>>>16];}
}
for(let j=0;j<gs.length;j++){const g=gs[j];if(g[0]>negative[g[0]])continue;const P=axis.map(r=>ar[g[r]]);let ms=0,md=0;for(let i=0;i<36;i++)if(P[i]<16){if(i<16)ms|=1<<i;else md|=1<<(i-16);}
 const key=ms+65536*md;if(!sections.has(key))sections.set(key,{ms,md,t:new Lut(P)});if(ms===65535)h.push(new Lut(P));
 let vis=0n,cy=[];for(let i=0;i<36;i++)if(!(vis&(1n<<BigInt(i)))){let z=i,m=0;do{vis|=1n<<BigInt(z);m++;z=P[z];}while(z!==i);cy.push(m);}cy.sort((a,b)=>a-b);const q=cy.join();gstats.set(q,(gstats.get(q)||0)+1);
}
if(sections.size!==27||h.length!==1920)throw Error('projective D5 orbit');
for(const [key,c] of gstats){const a=new Float64Array(K+1);a[0]=1;for(const l of key.split(',').map(Number))for(let j=K;j>=l;j--)a[j]+=a[j-l];burn+=a[K]*c;}
if(burn%51840)throw Error('Burnside');burn/=51840;
const cspin=new Int32Array(65536).fill(-1),xspin=new Int16Array(65536),stab=new Map();
for(let x=0;x<65536;x++){if(cspin[x]>=0)continue;let st=[];for(let j=0;j<h.length;j++){
 const y=h[j].s(x,0);cspin[y]=x;if(x===y)st.push(j);
 }stab.set(x,st);}
for(let x=0;x<65536;x++){let j=h.findIndex(v=>v.s(x,0)===cspin[x]);if(j<0)throw Error('spin transporter');xspin[x]=j;}
const secs=[...sections.values()].filter(x=>x.ms!==65535);
function* universes(){let ct=0;for(const [s,H] of stab){const n=pop(s);if(n<Math.ceil(4*K/9)||n>K)continue;const k=K-n,mark=new Uint8Array(1<<20),limit=1<<20;
 function canonD(s,d){let b=d;for(const j of stab.get(s)){const v=h[j].de(d);if(v<b)b=v;}return b;}
 for(let d=(1<<k)-1;d<limit;){const a=d&-d,b=d+a,next=a?(b|(((b^d)/a)>>>2)):limit;if(!mark[d]){
 for(const j of H)mark[h[j].de(d)]=1;
 let ok=true;for(const sec of secs){const nn=pop(s&sec.ms)+pop(d&sec.md);if(nn>n){ok=false;break;}if(nn===n){const x=sec.t.s(s,d),c=cspin[x];if(c<s){ok=false;break;}if(c===s){const v=sec.t.d(s,d);if(canonD(c,h[xspin[x]].de(v))<d){ok=false;break;}}}}
 if(ok){ct++;yield [s,d];}}
 d=next;}
 }if(ct!==burn)throw Error('orbit check '+ct+' / '+burn);
}
const buckets=new Map(),mcount=0;let count=0,per=[];
for(const T of types){if(!T.via||T.t===25||!T.h.length)continue;const seed=[...seeds.values()].find(t=>(t.m&T.m)===t.m);if(!seed)throw Error('seed');const core=types[seed.k].ids.map(i=>gs[seed.j][i]),used=new Set();
 for(let j=0;j<gs.length;j++){const g=gs[j],M=pm(T.ids,g);if(used.has(M))continue;used.add(M);const v={m:M,j,k:T.t,ps:0,pd:0,ns:0,nd:0,s:0,d:0};
  for(const i of T.ids){let r=g[i],u=ar[r],pos=axis[u]===r;if(u<16){v.s|=1<<u;if(pos)v.ps|=1<<u;else v.ns|=1<<u;}else{v.d|=1<<(u-16);if(pos)v.pd|=1<<(u-16);else v.nd|=1<<(u-16);}}
  let a=0,b=0;for(const i of core){const u=ar[g[i]];if(u<16)a|=1<<u;else b|=1<<(u-16);}const key=a+65536*b;if(!buckets.has(key))buckets.set(key,{a,b,vs:[]});buckets.get(key).vs.push(v);count++;
 }per.push([T.t,used.size]);}
if(count!==357444)throw Error('signed dictionary '+count);
const bins=[...buckets.values()];console.log('READY AXES',burn,bins.length,count);
function getV(s,d){let V=[];for(const o of bins){if((o.a&~s)||(o.b&~d))continue;for(const v of o.vs)if(!(v.s&~s)&&!(v.d&~d))V.push(v);}return V;}


const totals={signedOnly:0,orientedNonempty:0,orientedFew:0,orientedDeg:0,orientedColor:0,orientedTree:0,equator:0,empty:0,colors:0,recolor:0,hall:0};
function problem(s,d){
 if(pop(d)<=1){totals.equator++;return {nodes:0,max:0};}
 const V=getV(s,d);if(!V.length){totals.empty++;return {nodes:0,max:0};}
 const bits=[...new Set(V.flatMap(v=>types[v.k].ids.map(j=>gs[v.j][j])))],idx=new Map(bits.map((v,i)=>[v,i])),B=bits.length;
 const masks=V.map(v=>types[v.k].ids.map(j=>idx.get(gs[v.j][j]))),L=V.length,conf=new Map();
 function conflict(i,j){if(i>j)[i,j]=[j,i];const k=i*L+j;if(conf.has(k))return conf.get(k);const a=incompatible(V[i],V[j]);conf.set(k,a);return a;}

 const bb=masks.map(ro=>ro.reduce((q,r)=>q|1<<r,0)),bitOf=x=>31-Math.clz32(x&-x);if(B>32)throw Error('bit width');
 const perm=Array.from({length:L},(_,i)=>i),score=new Int32Array(L);
 function rainbow() {
  let nodes=0;const assignment=new Int8Array(L).fill(-1);
  function rec(vs,opts){if(!vs.length){for(let i=0;i<L;i++){if(!masks[i].includes(assignment[i]))throw Error('invalid list color');for(let j=0;j<i;j++)if(assignment[i]===assignment[j]&&!conflict(i,j))throw Error('invalid local SDR');}return true;}if(++nodes>800)return false;
   let best=999,x=-1,kd=-1;for(const i of vs){const t=pop(opts[i]),k=score[i];if(t<best||t===best&&k>kd){best=t;x=i;kd=k;}if(!best)return false;}
   const pp=vs.filter(t=>t!==x),actions=[];for(let b=opts[x];b;b&=b-1){const bit=b&-b;let sum=0,drop=false;const edit=[];for(const j of pp){if(!(opts[j]&bit)||conflict(j,x))continue;const t=pop(opts[j]);if(t===1){drop=true;break;}sum+=1/(t-1);edit.push(j);}
    if(!drop)actions.push([sum,bit,edit]);}
   actions.sort((a,b)=>a[0]-b[0]);for(const [,b,edit]of actions){assignment[x]=bitOf(b);for(const j of edit)opts[j]^=b;if(rec(pp,opts))return true;for(const j of edit)opts[j]|=b;if(nodes>800)break;}return false;
  }for(let i=0;i<L;i++){let n=0;for(let j=0;j<i;j++)if((bb[i]&bb[j])&&!conflict(i,j)){score[j]++;n++;}score[i]=n;}
  return rec(perm,bb.slice());
 }
 if(L>=15&&rainbow()){totals.colors++;return {nodes:1,max:L,rainbow:true};}

 function recolor(){
  const F=masks.map(rr=>rr.map(()=>[])),ind=Array.from({length:L},()=>new Int8Array(B).fill(-1));
  for(let i=0;i<L;i++)masks[i].forEach((b,k)=>ind[i][b]=k);
  for(let i=1;i<L;i++)for(let j=0;j<i;j++){let o=bb[i]&bb[j];if(!o||conflict(i,j))continue;for(;o;o&=o-1){const b=bitOf(o);F[i][ind[i][b]].push(j);F[j][ind[j][b]].push(i);}}
  let seed=19937;function rand(n){seed=(Math.imul(1664525,seed)+1013904223)>>>0;return Math.floor(seed/4294967296*n);}
  for(let pass=0;pass<12;pass++){const col=masks.map((r,i)=>r[rand(r.length)]),counts=F.map((rs,i)=>rs.map((rs,k)=>rs.filter(j=>col[j]===masks[i][k]).length));
   let cur=col.reduce((a,b,i)=>a+counts[i][ind[i][b]],0)/2,min=cur,stale=0;
   for(let step=0;step<100*L;step++){if(!cur){for(let i=0;i<L;i++){const k=ind[i][col[i]];if(k<0||F[i][k].some(j=>col[j]===col[i]))throw Error('invalid coloring');}return true;}
    let bads=[];for(let i=0;i<L;i++)if(counts[i][ind[i][col[i]]])bads.push(i);const v=bads[rand(bads.length)],old=ind[v][col[v]],c=counts[v];let best=10000,opts=[];
    for(let k=0;k<c.length;k++)if(k!==old){if(c[k]<best){best=c[k];opts=[k];}else if(c[k]===best)opts.push(k);}
    let k=opts[rand(opts.length)];if(stale>100&&rand(20)===0){k=rand(c.length-1);if(k>=old)k++;}const b=masks[v][k];
    cur+=c[k]-c[old];for(const j of F[v][old])counts[j][ind[j][col[v]]]--;for(const j of F[v][k])counts[j][ind[j][b]]++;col[v]=b;
    if(cur<min){min=cur;stale=0;}else stale++;if(stale>6*L)break;
   }
  }return false;
 }
 if(L>=15&&recolor()){totals.recolor++;return {nodes:1,max:L,recolored:true};}
 function singleGap(){
 const axes=[...new Set(V.flatMap(v=>types[v.k].ids.map(j=>ar[gs[v.j][j]])))].sort((a,b)=>a-b);if(axes.length<16)return {hits:0,total:0,ct:0,small:0,deg:0,col:0,tree:0};if(axes.length!==16)throw Error('axis coverage');
 const rm=V.map(v=>types[v.k].ids.map(j=>gs[v.j][j])),ii=new Map(axes.map((v,i)=>[v,i])),pos=rm.map(row=>row.reduce((q,r)=>q|(axis[ar[r]]===r?1<<ii.get(ar[r]):0),0)),neg=rm.map(row=>row.reduce((q,r)=>q|(axis[ar[r]]!==r?1<<ii.get(ar[r]):0),0));
 let total=0,small=0,deg=0,col=0,tree=0,hits=0,maxL=0,maxNodes=0,ct=0;
 for(let j=0;j<16;j++){const b=1<<j,fix=j===0?2:1,space=65535^b,bag=new Map();
 for(let v=0;v<L;v++){const P=pos[v]&space,N=neg[v]&space;if(N&fix)continue;const free=space&~(P|N|fix),base=P|fix;for(let a=free;;a=(a-1)&free){const w=base|a;if(!bag.has(w))bag.set(w,[]);bag.get(w).push(v);if(!a)break;}}
 total+=16384;for(const [u,C]of bag){if(C.length<18){small++;continue;}maxL=Math.max(maxL,C.length);const O=new Uint16Array(72);for(const v of C)for(const r of rm[v])O[r]++;
 let ok=true;for(let k=0;k<16;k++){const r=axis[axes[k]],q=negative[r];if(((k===j||(u>>k&1))&&O[r]<2)||((k===j||!(u>>k&1))&&O[q]<2)){ok=false;break;}}if(!ok){deg++;continue;}
 const groups=[];for(const i of C){let g=groups.find(w=>w.every(j=>conflict(i,j)));if(!g){g=[];groups.push(g);}g.push(i);}if(groups.length<18){col++;continue;}
 let nodes=0;function go(P,t){if(P.length<t)return false;if(t<=1)return true;if(++nodes>25000)return null;const cs=[];for(const a of P){let q=cs.find(h=>h.every(z=>conflict(a,z)));if(!q){q=[];cs.push(q);}q.push(a);}
 for(let k=cs.length-1;k>=t-1;k--){const prev=cs.slice(0,k).flat();for(const v of cs[k]){const z=go(prev.filter(w=>!conflict(v,w)),t-1);if(z!==false)return z;}}return false;}
 let ans=go(C,18);
 if(ans!==false){
  const rootsMissing=[...new Set(C.flatMap(i=>rm[i]))];
  if(rootsMissing.length!==17)throw Error('missing sign support');
  if(rootsMissing.some(r=>{const W=C.filter(i=>rm[i].includes(r));for(let i=1;i<W.length;i++)for(let j=0;j<i;j++)if(!conflict(W[i],W[j]))return false;return true;}))ans=false;
  if(ans!==false){
   const byMask=new Map(C.map(v=>[V[v].m,v]));
   const bfs=opts(rootsMissing).filter(t=>types[t.k].via&&t.k!==25&&types[t.k].h.length).map(t=>byMask.get(t.m));
   if(bfs.length!==C.length||new Set(bfs).size!==C.length||bfs.includes(undefined))throw Error('site ordering');
   const orders=[bfs,C.slice().sort((a,b)=>V[a].k-V[b].k||(V[a].m<V[b].m?-1:1)),bfs.slice().reverse()];
   for(const W of orders){nodes=0;ans=go(W,18);if(ans!==null)break;}
  }
 }
 maxNodes=Math.max(maxNodes,nodes);if(ans!==false){hits++;}else tree++;
 }ct+=bag.size;}
 return {total,ct,small,deg,col,tree,hits,maxL,maxNodes};
}
 if(L>=350){const q=singleGap();if(!q.hits){totals.signedOnly++;totals.orientedNonempty+=q.ct;totals.orientedFew+=q.small;totals.orientedDeg+=q.deg;totals.orientedColor+=q.col;totals.orientedTree+=q.tree;return {nodes:1,max:L};}}
 totals.hall++;
 let nodes=0,peak=0,ob=null;
 function go(P){nodes++;if(nodes>30000)throw 'budget';peak=Math.max(peak,P.length);
  if(P.length<=5)return false;
  const match=new Int32Array(B).fill(-1),paired=new Set();let l=0;
  for(const v of P){const seen=new Int8Array(B);function aug(q){for(const b of masks[q]){if(seen[b])continue;seen[b]=1;if(match[b]<0||aug(match[b])){match[b]=q;return true;}}return false;}if(aug(v)){l++;paired.add(v);}}
  if(l===P.length)return false;
  // The left alternating forest rooted at unmatched sites is an explicit deficient Hall subset.
  const S=P.filter(v=>!paired.has(v)),marked=new Set(S),sign=new Int8Array(B);for(let a=0;a<S.length;a++)for(const b of masks[S[a]]){if(sign[b])continue;sign[b]=1;const v=match[b];if(v>=0&&!marked.has(v)){marked.add(v);S.push(v);}}
  if(S.length<P.length)return go(S);
  const parent=Array.from({length:B},(_,i)=>i);function root(i){while(parent[i]!==i){parent[i]=parent[parent[i]];i=parent[i];}return i;}for(const v of S){let a=root(masks[v][0]);for(const k of masks[v])parent[root(k)]=a;}
  let comp=new Map();for(const v of S){const k=root(masks[v][0]);if(!comp.has(k))comp.set(k,[]);comp.get(k).push(v);}if(comp.size>1){for(const C of comp.values())if(go(C))return true;return false;}
  const used=sign.reduce((a,b)=>a+b,0);if(S.length<=used)throw Error('Hall witness');
  let bad=null;const deg=new Map();
  for(let i=1;i<S.length;i++)for(let j=0;j<i;j++)if(conflict(S[i],S[j])){deg.set(S[i],(deg.get(S[i])||0)+1);deg.set(S[j],(deg.get(S[j])||0)+1);}
  if(!deg.size){ob=S.map(i=>V[i].m.toString());return true;}
  let x=-1,best=-1;for(const [i,k]of deg)if(k>best){best=k;x=i;}
  // Every clique either excludes x or excludes all conflicting neighbors of x.
  return go(P.filter(v=>v!==x))||go(P.filter(v=>v===x||!conflict(x,v)));
 }
 let found=false,unknown=false;try{found=go(Array.from({length:L},(_,i)=>i));}catch(e){if(e!=='budget')throw e;unknown=true;}return {nodes,max:L,found,unknown,ob};
}
const first=Number(process.argv[2]||0),last=Number(process.argv[3]||149490);if(!Number.isInteger(first)||!Number.isInteger(last)||first<0||first>=last||last>149490)throw Error('invalid orbit interval');let visited=0;let c=0,tot=0,hard=0,max=0,res=[],st=Date.now();for(const [s,d] of universes()){
 const ix=c++;if(ix<first||ix>=last)continue;visited++;const z=problem(s,d);tot+=z.nodes;max=Math.max(max,z.max);if(z.unknown||z.found){res.push([s,d,z.unknown?'?':z.ob]);if(res.length<=5)console.log('example',s,d,JSON.stringify(z));}
 if(Date.now()-st>20000){console.log('FRAME',K,c,tot,max,res.length);st=Date.now();}
}console.log('FRAME FINAL',K,c,burn,tot,max,res.length,JSON.stringify(totals),JSON.stringify(res.slice(0,10)));console.log('SHARD',first,last,visited);if(c!==burn||c!==149490||visited!==last-first||res.length)throw Error('unresolved orbits');}