'use strict';
const summary = (() => {


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
for(let k=0;k<5;k++){
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
if(stars.length!==2||forks.length!==1)throw Error("wrong mask types");
const reverse=w=>[w[4],w[3],w[2],w[1],w[0],w[5]];
const lab=C=>C.map(r=>r.join()).sort().join(';');
if(lab(stars[0].map(reverse))!==lab(stars[1]))throw Error("diagram symmetry");
const C=stars.find(C=>C.every(r=>r[1]===2n));
if(!C)throw Error("star orientation");
function vertices(C){
  const U=maximal(positive.filter(r=>!C.includes(r))), L=minimal(C);
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
const fork=vertices(forks[0]), h=H.map(v=>12n*v);
if(fork.length!==7||fork.some(w=>norm(w)>2n*determinant*144n||
    norm(w)===2n*determinant*144n&&w.join()!==h.join()))throw Error("fork sphere");
const star=vertices(C);
const axis=(i,q)=>E[i].map(v=>BigInt(q)*v);
const pair=(i,j,q)=>axis(i,q).map((v,k)=>v+axis(j,q)[k]);
const expected=[axis(5,12),axis(2,6),axis(1,12),axis(1,6),pair(1,4,6),pair(1,3,4),axis(0,12)];
if(star.length!==7||!star.every(w=>expected.some(x=>x.join()===w.join())))throw Error("star vertices");
const v=axis(0,12);
const top=axis(1,12), midpoint=v.map((x,i)=>(x+top[i])/2n);
if(norm(midpoint)!==2n*determinant*144n || norm(v)>=2n*determinant*144n ||
    star.some(w=>w.join()!==top.join()&&norm(w)>2n*determinant*144n))throw Error("norm clipping");
const sum=a=>a.reduce((s,x)=>s+x,0n);
// a_i are inner products with the five roots, and eta measures the orthogonal component times sqrt(2).
const table=expected.map(w=>{
  const a=C.map(r=>dot(r,w)), eta=w.join()===v.join()?12n:0n;
  const scaledNorm=6n*dot(a,a)-sum(a)**2n+3n*eta*eta;
  if(scaledNorm*determinant!==6n*norm(w))throw Error("projective coordinates");
  return {a,eta};
});
const V=table.pop();
const clipped=[...table,...table.map(({a})=>({a:a.map((v,i)=>(v+V.a[i])/2n),eta:V.eta/2n}))];
const norm6=({a,eta})=>6n*dot(a,a)-sum(a)**2n+3n*eta*eta;
let comparisons=0,equalities=0;
for(let i=0;i<clipped.length;i++)for(let j=i;j<clipped.length;j++){
  const p=clipped[i],q=clipped[j];
  const a=p.a.slice().sort((u,v)=>Number(u-v)), b=q.a.slice().sort((u,v)=>Number(v-u));
  const d=6n*dot(a,b)-sum(a)*sum(b)-3n*p.eta*q.eta;
  const gap=4n*d*d-norm6(p)*norm6(q);
  if(d<=0n||gap<0n)throw Error("vertex cosine");
  if(!gap){if(i||j)throw Error("nonroot equality");equalities++;}
  comparisons++;
}
const mask=ids=>ids.reduce((b,i)=>b|(1n<<BigInt(i)),0n);
const masks=[C.map(r=>index.get(r.join()))], known=new Set(masks.map(mask));
for(let i=0;i<masks.length;i++){
  const moves=[...I.map(k=>r=>reflect(r,k)),reverse];
  for(const f of moves){
    const ids=masks[i].map(j=>index.get(f(roots[j]).join()));
    const key=mask(ids);
    if(!known.has(key)){known.add(key);masks.push(ids);}
  }
}
const negative=roots.map(r=>index.get(r.map(v=>-v).join()));
const signed=masks.map(mask), full=masks.map(ids=>mask([...ids,...ids.map(i=>negative[i])]));
const counts={};
for(let i=0;i<masks.length;i++)for(let j=i+1;j<masks.length;j++){
  if(full[i]&full[j])continue;
  const U=signed[i]|signed[j];
  const k=signed.filter(m=>(m&U)===m).length;
  counts[k]=(counts[k]??0)+1;
}
if(comparisons!==78||equalities!==1||masks.length!==432||counts[2]!==38880||counts[3]!==8640||Object.keys(counts).length!==2)throw Error("census");
return {forkVertices:fork.length,starVertices:star.length,comparisons,equalities,signedMasks:masks.length,counts};
})();
console.log(summary);
