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

function incompatible(a,b){
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
function clique(V,n){
 if(n<=0)return true;if(V.length<n)return false;
 const colors=[];for(const a of V){const c=colors.find(c=>c.every(b=>incompatible(a,b)));if(c)c.push(a);else colors.push([a]);}
 if(colors.length<n)return false;
 for(let c=colors.length-1;c>=n-1;c--){const prev=colors.slice(0,c).flat();for(const a of colors[c])if(clique(prev.filter(b=>!incompatible(a,b)),n-1))return true;}
 return false;
}
const rg=roots.map(v=>v.map(Number));const pids=getMask(positive),rho=I.map(k=>pids.reduce((a,id)=>a+rg[id][k],0)/2);
const dg=Number(determinant);
const targets=[];
function gen(y,k,v){if(k===6){if(v.some(x=>x%dg))return;targets.push({y:y.slice(),d:rho.map((x,i)=>x-v[i]/dg)});return;}
 for(let n=0;I.every(i=>v[i]+n*adjN[i][k]<=rho[i]*dg);n++)gen(y.concat([n]),k+1,I.map(i=>v[i]+n*adjN[i][k]));
}gen([],0,[0,0,0,0,0,0]);
const key=v=>((((v[0]*64+v[1])*64+v[2])*64+v[3])*64+v[4])*64+v[5];
function half(ids){const t=new Map();let v=[0,0,0,0,0,0],old=0;for(let h=0;h<1<<ids.length;h++){let b=h^(h>>1);if(h){const pos=31-Math.clz32(b^old),sign=(b>>pos&1)?1:-1,r=rg[ids[pos]];for(let k=0;k<6;k++)v[k]+=sign*r[k];}old=b;const kk=key(v);let line=t.get(kk);if(!line)t.set(kk,line={v:v.slice(),bits:[]});line.bits.push(b);}return t;}
const X=half(pids.slice(0,18)),Y=half(pids.slice(18)),ims=permutations.map(p=>pids.map(id=>{const i=p[id],j=pids.indexOf(i);return j>=0?[j,0]:[pids.indexOf(negative[i]),1];}));const T18=2**18,mask18=T18-1;
const tab=ims.map(im=>{let fl=0,fh=0;for(const [j,f] of im)if(f){if(j<18)fl^=1<<j;else fh^=1<<(j-18);}
 const l=[],h=[];for(let q=0;q<4;q++){const a=new Int32Array(512),b=new Int32Array(512);for(let f=1;f<512;f++){const bit=f&-f,k=31-Math.clz32(bit),j=im[q*9+k][0];a[f]=a[f^bit]^(j<18?1<<j:0);b[f]=b[f^bit]^(j>=18?1<<(j-18):0);}l.push(a);h.push(b);}return {fl,fh,l,h};});
const maskAct=(v,i)=>{const hi=Math.floor(v/T18),lo=v-hi*T18,x=tab[i],a=lo&511,b=lo>>9,c=hi&511,d=hi>>9;return (x.fl^x.l[0][a]^x.l[1][b]^x.l[2][c]^x.l[3][d])+T18*(x.fh^x.h[0][a]^x.h[1][b]^x.h[2][c]^x.h[3][d]);};
function orbitList(y,d,callback){const comp=reverse(y).join().localeCompare(y.join());if(comp<0)return [0,0];const st=I.filter(i=>!y[i]);if(!comp)st.push(6);
 const hh=new Set();for(const {v,bits} of X.values()){const w=I.map(i=>d[i]-v[i]);if(w.some(x=>x<0))continue;const b2=Y.get(key(w));if(!b2)continue;for(const u of bits)for(const v of b2.bits)hh.add(u+v*T18);}
 let count=0,n=hh.size;for(const b of hh){if(!hh.delete(b))continue;const fringe=[b];for(let i=0;i<fringe.length;i++)for(const a of st){const m=maskAct(fringe[i],a);if(hh.delete(m))fringe.push(m);}++count;callback(b,fringe.length);}
 return [count,n];}
function signedMask(b){const lo=b%T18,hi=Math.floor(b/T18);return pids.map((r,i)=>(i<18?lo>>i&1:hi>>(i-18)&1)?negative[r]:r);}
function sponsor(u,cand,tries=6){
 const lists=new Map(cand.map(t=>[t,u.filter(r=>t.m&bit[r])]));
 let rnd=7346331;const rng=()=>rnd=(rnd*1664525+1013904223)>>>0;let best=0;
 for(let t=0;t<tries;t++){const buckets=new Map(u.map(r=>[r,[]])), pr=new Map(cand.map(t=>[t,rng()]));
 const M=cand.slice().sort((a,b)=>lists.get(a).length-lists.get(b).length||pr.get(a)-pr.get(b));let k=0;
 for(const a of M){const cs=lists.get(a).filter(r=>buckets.get(r).every(b=>incompatible(a,b)));if(!cs.length)break;
 cs.sort((r,s)=>buckets.get(r).length-buckets.get(s).length);buckets.get(cs[0]).push(a);k++;}
 if(k===M.length){const seen=new Set();for(const [r,v] of buckets){for(let i=0;i<v.length;i++){if(!(v[i].m&bit[r])||seen.has(v[i]))throw Error("nonlist color");seen.add(v[i]);for(let j=0;j<i;j++)if(!incompatible(v[i],v[j]))throw Error("not proper");}}if(seen.size!==cand.length)throw Error("incomplete");return [true,t,k];}if(k>best)best=k;
 }return [false,best];
}

let counts={},maxGeometric=0,spons=0,scoreCount=0,scoreFail=0,just=[],maxNodes=0;const sum=orbitList([0,0,0,0,0,0],rho,(b,n)=>{const U=signedMask(b),C=opts(U).filter(t=>types[t.k].h.length>0);
 const colors=[];for(const a of C){const cl=colors.find(g=>g.every(z=>incompatible(a,z)));if(cl)cl.push(a);else colors.push([a]);}let k=colors.length;while(k&&!clique(C,k))--k;counts[k]=(counts[k]||0)+1;maxGeometric=Math.max(k,maxGeometric);
 const s=sponsor(U,C,12);if(s[0])spons++;else throw Error('no valid list coloring');
});console.log(JSON.stringify({sum,counts,maxGeometric,spons}));if(sum[0]!==156||sum[1]!==13697920||maxGeometric!==12||spons!==156||JSON.stringify(counts)!=='{"0":2,"3":1,"4":9,"5":23,"6":53,"7":39,"8":10,"9":15,"12":4}')throw Error('census');}
