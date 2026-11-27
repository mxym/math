'use strict';
// Run with Node.js. Fundamental chamber coordinates are simple-root inner products.



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

function vertices(C){
  const U=maximal(positive.filter(r=>!C.includes(r))), L=minimal(C);
  
  if(I.some(i=>!U.some(r=>r[i]>0n)))throw Error('unbounded chamber coordinate');
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

const assert=require('node:assert/strict'), ds=144n*determinant;
const Gdot=(r,s)=>dot(r,G.map(row=>dot(row,s)));
let ideals=[[]], totals=[],bad=[],baseMax=0n;
for(let k=0;k<=4;k++){
  let count=0;
  for(const a of ideals){
    const C=a.map(i=>positive[i]), V=vertices(C);count+=V.length;
    for(const v of V){
      const B=positive.filter(r=>dot(r,v)>12n);
      if(!B.length){if(norm(v)>baseMax)baseMax=norm(v);assert(3n*norm(v)<=4n*ds);continue;}
      const bary=I.map(j=>12n*B.reduce((s,r)=>s+dot(G[j],r),0n));
      if(v.every((x,i)=>x*BigInt(B.length)===bary[i]))continue;
      assert.equal(k,4);assert.equal(B.length,4);assert.equal(6n*norm(v),11n*ds);
      assert(B.every(r=>dot(r,v)===18n));bad.push({roots:a,scaled:v.map(Number)});
    }
  }
  totals.push([k,ideals.length,count]);
  const next=new Map();for(const a of ideals)for(const r of maximal(positive.filter((_,i)=>!a.includes(i)))){
    const b=[...a,positive.indexOf(r)].sort((x,y)=>x-y);next.set(b.join(),b);
  }ideals=[...next.values()];
}
assert.equal(3n*baseMax,4n*ds);assert.equal(bad.length,2);
// For any fixed x there are ten decompositions x=y+z with y·z=-1.
// The twenty y,z are on distinct axes (each has x-inner-product +1).
const Rset=new Set(roots.map(r=>r.join()));for(const x of roots){const Y=roots.filter(y=>Rset.has(x.map((v,i)=>v-y[i]).join()));assert.equal(Y.length,20);assert(Y.every(y=>Gdot(x,y)===1n));}
console.log('chamber cells and vertex incidences:',totals,'first non-barycentric vertices:',bad);
