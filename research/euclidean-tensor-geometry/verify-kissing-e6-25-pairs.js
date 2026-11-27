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
if(determinant!==3n)throw Error('E6 Cartan determinant');
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
for(let k=0;k<6;k++){
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
if(groups.length!==3||det(groups[0])!==-1n||det(groups[1])!==0n||det(groups[2])!==1n||lab(groups[0].map(reverse))!==lab(groups[2]))throw Error('six ideal types');
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
const N0=2n*determinant*144n, globalHighest=H;
function sliceHull(vs){
 const high=vs.filter(v=>norm(v)>N0), low=vs.filter(v=>norm(v)<=N0), M=96n;
 const H=low.filter(v=>norm(v)===N0), root=v=>v.every((x,i)=>x===12n*globalHighest[i]);
 if(vs.length!==7||!H.some(root))throw Error('six chamber vertices');
 if(!high.length){
  if(H.length!==2)throw Error('middle sphere slice');
  return H;
 }
 if(H.length!==1)throw Error('extra six norm-two vertex');
 if(high.length!==1)throw Error("more than one high");
 const U=high[0], gen=[U.map(x=>x*M)];
 for(const V of low){
  let t=M;
  const at=t=>U.map((u,i)=>u*t+V[i]*(M-t));
  while(norm(at(t))>N0*M*M)t--;
  if(root(V)&&t!==0n)throw Error('highest root clipped off');
  gen.push(at(t));
 }
 return gen;
}
const bil=(a,b)=>dot(a,adj.map(row=>dot(row,b)));
function test(C){
 const H=sliceHull(vertices(C));
 const M=C.map(r=>C.map(s=>gram(r,s)));
 let excluded=det(C)?-1:C.findIndex((_,k)=>I.some(j=>det(C.filter((_,i)=>i!==k).concat([E[j]]))));
 const basis=C.filter((_,i)=>i!==excluded);
 let n=null;
 if(excluded>=0){
    const Gbasis=basis.map(r=>G.map(row=>dot(row,r)));
    n=I.map(i=>BigInt(i%2?-1:1)*det(Gbasis.map(row=>row.filter((_,j)=>i!==j))));
    if(n.every(v=>!v))throw Error("orthogonal");
 }
 let checked=0, eq=0;
 for(const p of permutationsSmall(I)){
  if(I.some(i=>I.some(j=>M[i][j]!==M[p[i]][p[j]])))continue;
  for(const sign of n?[1n,-1n]:[1n]){
   const matrix=n?basis.concat([n]):basis;
   for(let i=0;i<H.length;i++){
    const q=H[i], vals=p.filter((_,j)=>j!==excluded).map(j=>dot(C[j],q));
    if(n)vals.push(sign*dot(n,q));
    const {y,d}=solve(matrix,vals);
    if(norm(y)!==d*d*norm(q))throw Error("not isometry");
    for(let j=0;j<H.length;j++){
     checked++;const a=H[j], u=bil(a,y),gap=4n*u*u-norm(a)*norm(y);
     if(u<=0n||gap<0n)throw Error('same-mask separation');
     if(gap===0n){if(a.some((v,k)=>k!==5&&v)||q.some((v,k)=>k!==5&&v))throw Error('same-mask nonroot equality');eq++;}
    }
   }
  }
 }
 return {checked,eq};
}
const checks=groups.map(test);
if(JSON.stringify(checks.map(({checked,eq})=>[checked,eq]))!==JSON.stringify([[588,8],[128,16],[588,8]]))throw Error("six-mask comparison count");
console.log({sameSixMask:checks.map(({checked,eq})=>[checked,eq])});

const F=groups5.find(C=>C.every(r=>r[1]===2n)), V=E[0].map(v=>12n*v);
const Fh=vertices(F).filter(w=>w.join()!==V.join()).flatMap(w=>[w.map(v=>2n*v),w.map((v,i)=>v+V[i])]);
const sum=a=>a.reduce((s,x)=>s+x,0n);
const make=(C,w)=>{
 const a=C.map(r=>dot(r,w)).sort((u,v)=>Number(u-v));
 const q=6n*norm(w)/determinant; if(6n*norm(w)%determinant)throw Error("norm not integrally scaled");
 const etaNumerator=q-6n*dot(a,a)+sum(a)**2n;
 if(etaNumerator<0n||etaNumerator%3n)throw Error('bad normal norm');
 const eta2=etaNumerator/3n;
 const eta=BigInt(Math.round(Math.sqrt(Number(eta2))));
 if(eta*eta!==eta2)throw Error("bad eta");
 return {a,eta,q,isRoot:w.every((v,k)=>k===5||v===0n)};
};
const facts=[];
for(const C of groups)for(const k of I){
 const B=C.filter((_,i)=>i!==k);
 if(!isStar(B))continue;
 let pairs=0,eq=0;
 for(const x of Fh.map(w=>make(F,w)))for(const y of sliceHull(vertices(C)).map(w=>make(B,w))){
  const z=6n*dot(x.a,[...y.a].reverse())-sum(x.a)*sum(y.a)-3n*x.eta*y.eta;
  const gap=4n*z*z-x.q*y.q;
  pairs++;
  if(z<=0n||gap<0)bad++;
  if(gap===0n&&z>0)eq++;
 }
 facts.push([pairs,eq]);
}
if(JSON.stringify(facts)!=='[[84,1],[84,1]]')throw Error('mixed census');console.log({mixed:facts});

const C5=groups5.find(C=>C.every(r=>r[1]===2n)), ids5=getMask(C5);
const Fs=new Set(orbit(ids5).map(mask)), Ss=new Set(groups.flatMap(C=>orbit(getMask(C)).map(mask)));
if(Fs.size!==432||Ss.size!==15120)throw Error('mask orbit size');
const bit=roots.map((_,i)=>1n<<BigInt(i));
const fiveL=orbit(ids5), sixL=groups.flatMap(C=>orbit(getMask(C)));
const seen=new Set(), tab={};
function examine(U){
 const u=mask(U);if(seen.has(u))return;seen.add(u);
 const ms=[];
 function scan(i,k,m){if(k===0){if(Fs.has(m)||Ss.has(m))ms.push(m);return;}
  for(let j=i;j<=11-k;j++)scan(j+1,k-1,m|bit[U[j]]);
 }
 scan(0,5,0n);scan(0,6,0n);
 const edges=[];
 for(let i=0;i<ms.length;i++)for(let j=i+1;j<ms.length;j++)if(!(ms[i]&ms[j]))edges.push([i,j]);
 const matching2=edges.some(([a,b],i)=>edges.slice(i+1).some(([c,d])=>c!==a&&c!==b&&d!==a&&d!==b));
 for(const [a,b] of edges)for(const [c,d] of edges){
  if(a===c||a===d||b===c||b===d)continue;
  const inc=(x,y)=>{const u=ms[x]&ms[y];return u===ms[x]||u===ms[y];};
  if(!inc(a,c)&&!inc(a,d)&&!inc(b,c)&&!inc(b,d))throw Error("matching survives");
 }
 const cover1=edges.some(([i])=>edges.every(edge=>edge.includes(i)))||edges.some(([,j])=>edges.every(edge=>edge.includes(j)));
 const key=[ms.length,edges.length,+cover1,+matching2].join();
 tab[key]=(tab[key]??0)+1;
}
const nS=id=>id.every(i=>!ids5.includes(i)&&!ids5.includes(negative[i]));
for(const D of fiveL){
 if(!nS(D))continue;
 const B=ids5.concat(D);
 for(const i of roots.keys())if(!B.includes(i)&&!B.includes(negative[i]))examine(B.concat([i]));
}
for(const D of sixL)if(nS(D))examine(ids5.concat(D));
if(seen.size!==14260||Object.entries(tab).reduce((s,[k,n])=>s+(k.endsWith(",1")?n:0),0)!==1200)throw Error("census");console.log({count:seen.size,withDisjointEdges:1200});
