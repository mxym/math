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
const stars=groups.filter(isStar), forks=groups.filter(C=>!isStar(C));
const reverse=w=>[w[4],w[3],w[2],w[1],w[0],w[5]];
const lab=C=>C.map(r=>r.join()).sort().join(';');
const C=stars.find(C=>C.every(r=>r[1]===2n));
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
const fiveBase=E /* dummy */;
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
 let B=inds.map(i=>inds.filter(j=>j!==i)).find(ids=>det(ids.map(i=>C[i])));
 if(!B)B=inds.flatMap(i=>inds.slice(i+1).map(j=>inds.filter(k=>k!==i&&k!==j))).find(ids=>I.some(j=>det(ids.map(i=>C[i]).concat([E[j]]))));
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
if(groups.length!==4||lab(groups[0].map(reverse))!==lab(groups[3]))throw Error('diagram');
// Distinct isomorphism types among all except the diagram-reversed pair.
for(const [j,k] of [[0,1],[0,2],[1,2]]){const A=groups[j],B=groups[k];if(permutationsSmall(A.map((_,i)=>i)).some(p=>A.every((u,i)=>A.every((v,h)=>gram(u,v)===gram(B[p[i]],B[p[h]])))))throw Error('unexpected mask equivalence');}
const z7=groups.map(test);if(z7.some(z=>z.bad)||z7.map(z=>z.checked).join()!=='196,5808,4704,196'||z7.map(z=>z.eq).join()!=='2,32,0,2')throw Error('seven capacity');
if(z7.some(z=>z.badPairs.some(([i,j])=>[i,j].some(k=>z.hull[k].split(',').some((x,r)=>r!==5&&x!=='0')))))throw Error('nonroot equality');
console.log({sameSeven:z7.map(({checked,eq})=>[checked,eq])});

const F=groups5.find(C=>C.every(r=>r[1]===2n)), V=E[0].map(v=>12n*v);
const Fh=vertices(F).filter(w=>w.join()!==V.join()).flatMap(w=>[w.map(v=>2n*v),w.map((v,i)=>v+V[i])]);
const sum=a=>a.reduce((s,x)=>s+x,0n);
const make=(C,w)=>{
 const a=C.map(r=>dot(r,w)).sort((u,v)=>Number(u-v));
 const q=6n*norm(w)/determinant; if(6n*norm(w)%determinant)throw Error("norm not integrally scaled");
 const nr=q-6n*dot(a,a)+sum(a)**2n;if(nr%3n||nr<0n)throw Error('orthogonal coordinate');const eta2=nr/3n;
 const eta=BigInt(Math.round(Math.sqrt(Number(eta2))));
 if(eta*eta!==eta2)throw Error("bad eta");
 return {a,eta,q,w};
};

const scales=new Map(groups.map(C=>[C,vertices(C).some(v=>norm(v)>N0)?1152n:12n]));
const sliceHullScale=C=>scales.get(C);
const facts=[];
for(const C of groups)for(const i of C.keys())for(let j=i+1;j<C.length;j++){
 const B=C.filter((_,k)=>k!==i&&k!==j);if(!isStar(B))continue;
 let pairs=0,bad=0,eq=0,min=1;
 for(const x of Fh.map(w=>make(F,w)))for(const y of sliceHull(vertices(C)).map(w=>make(B,w))){
  const z=6n*dot(x.a,[...y.a].reverse())-sum(x.a)*sum(y.a)-3n*x.eta*y.eta;
  // Actual second point has fixed squared norm 2, so compare linearly in its hull.
  // z/6 is the scaled inner product, x.q/6 the squared norm of x.w, and 1152 the scale of y.w.
  if(sliceHullScale(C)!==1152n)throw Error('seven-hull scale');
  const gap=z*z-3n*x.q*1152n**2n;
  pairs++;if(z<=0n||gap<0n)throw Error('mixed 5-7 linear bound');
  if(gap===0n){eq++;if(x.w.some((v,k)=>k!==5&&v!==0n))throw Error('nonroot 5-7 equality');}
 }
 facts.push([groups.indexOf(C),i,j,pairs,bad,eq,min]);
}
if(JSON.stringify(facts.map(v=>v[3]))!=='[84,132,132,84]')throw Error('5-7 census');console.log({mixedFiveSeven:facts.map(a=>[a[3],a[5]])});
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

const index6=[0,1,2,3,4,5];
function mixed6(B,A,p){
 let ids=index6, n=null;
 if(!det(A)){
  ids=index6.map(i=>index6.filter(j=>j!==i)).find(sel=>I.some(j=>det(sel.map(i=>A[i]).concat([E[j]]))));
  const ga=ids.map(i=>G.map(row=>dot(row,A[i])));
  n=I.map(i=>BigInt(i%2?-1:1)*det(ga.map(row=>row.filter((_,j)=>i!==j))));
 }
 const base=ids.map(i=>A[i]), bn=ids.map(i=>B[p[i]]);
 let n2=null;
 if(n){
  const gb=bn.map(r=>G.map(row=>dot(row,r)));
  n2=I.map(i=>BigInt(i%2?-1:1)*det(gb.map(row=>row.filter((_,j)=>i!==j))));
 }
 if(n&&gram(n,n)!==gram(n2,n2))throw Error("normal norm mismatch");
 let checked=0, bad=0,eq=0,min=2;
 for(const [k,w] of HB.entries())for(const sign of n?[1n,-1n]:[1n]){
   const vals=bn.map(r=>dot(r,w));if(n)vals.push(sign*dot(n2,w));
   const {y,d}=solve(n?base.concat([n]):base,vals);
   if(norm(y)!==d*d*norm(w))throw Error("bad norm");
   for(const [j,a] of HA.entries()){
    const u=bil(a,y), gap=4n*u*u-norm(a)*norm(y);
    if(u<=0n||gap<0n)bad++;
    if(gap===0n&&u>0n){if(a.some((v,k)=>k!==5&&v!==0n))throw Error('nonroot six equality');eq++;}
    checked++;min=Math.min(min,Number(u)/Math.sqrt(Number(norm(a)*norm(y))));
   }
 }
 return [checked,bad,eq,min];
}
let HB,HA;
const perms6=permutationsSmall(index6);
for(const [j,C] of groups.entries()){
 HB=sliceHull(vertices(C)); 
 for(const k of C.keys()){
  const B=C.filter((_,i)=>i!==k), thisGram=B.map(r=>B.map(s=>gram(r,s)));
  for(const [a,A] of groups6.entries()){
   const ag=A.map(r=>A.map(s=>gram(r,s)));
   const perms=perms6.filter(p=>index6.every(i=>index6.every(l=>ag[i][l]===thisGram[p[i]][p[l]])));
   if(!perms.length)continue;
   HA=sliceHull(vertices(A));
   const matches=perms.map(p=>mixed6(B,A,p));if(matches.some(v=>v[1]))throw Error('mixed six failed');
   console.log([j,k,a,matches.length,matches.reduce((s,v)=>s+v[0],0),matches.reduce((s,v)=>s+v[1],0),matches.reduce((s,v)=>s+v[2],0),Math.min(...matches.map(x=>x[3]))]);
  }
 }
}
