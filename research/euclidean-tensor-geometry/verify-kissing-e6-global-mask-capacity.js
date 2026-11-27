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
for(let k=0;k<0;k++){
  const next=new Map();
  for(const set of ideals)for(const r of maximal(positive.filter((_,i)=>!set.includes(i)))){
    const t=[...set,positive.indexOf(r)].sort((a,b)=>a-b);
    next.set(t.join(),t);
  }
  ideals=[...next.values()];
}
const groups=[];
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
 const perms=[];function enumG(p){const i=p.length;if(i===N){perms.push(p);return;}for(const j of inds)if(!p.includes(j)&&p.every((v,k)=>M[k][i]===M[v][j])&&M[i].map(String).sort().join()===M[j].map(String).sort().join())enumG([...p,j]);}enumG([]);
 for(const p of perms){
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

function nextIdeal(sets){const next=new Map();for(const S of sets)for(const r of maximal(positive.filter((_,i)=>!S.includes(i)))){const t=S.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(t.join(),t);}return [...next.values()];}
function exactMask(w){const N=norm(w);return roots.filter(r=>{const b=dot(r,w);return b>0n&&2n*determinant*b*b>N;});}
function checkDom(C){const s=I.map(k=>C.reduce((a,r)=>a+r[k],0n));for(const i of I){
 const b=dot(G[i],s),fixed=lab(C)===lab(C.map(r=>reflect(r,i)));if(b<0n||fixed!==(b===0n))throw Error('dominant ideal sum');
}}
let cur=[[]],hist=[];
for(let k=1;k<=16;k++){
 cur=nextIdeal(cur);if(k<8)continue;
 let comparisons=0,equalities=0;
 for(const S of cur){
  const C=S.map(i=>positive[i]);checkDom(C);
  const z=test(C);if(z.bad)throw Error('wrong cosine');
  const eligible=z.hull.map(key=>lab(exactMask(key.split(',').map(BigInt)))===lab(C));
  if(z.badPairs.some(([i,j])=>eligible[i]&&eligible[j]))throw Error('true equality-ray pair');
  comparisons+=z.checked;equalities+=z.eq;
 }
 hist.push([k,cur.length,comparisons,equalities]);
}
console.log({capacityChecks:hist});
const at17=nextIdeal(cur);
if(at17.length!==25)throw Error('seventeen ideals');
function lower(C){
 const rows=[...E,...minimal(C)], rhs=[...E.map(()=>0n),...minimal(C).map(()=>1n)];let cert=null;
 function go(ix,J){if(cert)return;
  if(J.length){
   const A=J.map(i=>rows[i]),b=J.map(i=>rhs[i]),K=A.map(u=>A.map(v=>gram(u,v))),detK=det(K);
   if(detK>0n){
    const c=A.map((_,i)=>det(K.map((row,j)=>row.map((w,k)=>k===i?b[j]:w))));
    if(c.every(t=>t>=0n)&&dot(c,b)>=2n*detK){cert=[J,c.map(String),String(detK),Number(dot(c,b))/Number(detK)];return;}
   }
  }
  if(J.length>=6)return;
  for(let j=ix;j<rows.length;j++)go(j+1,[...J,j]);
 }
 go(0,[]);return cert;
}

const outs=at17.map(ids=>lower(ids.map(i=>positive[i])));if(outs.some(x=>!x))throw Error('17 blockers not excluded');
if(exactMask(E[4]).length!==16)throw Error('sharpness');
console.log({seventeenIdeals:outs.length,lowerBounds:outs.map(x=>x[3]),sharpSixteen:true});
