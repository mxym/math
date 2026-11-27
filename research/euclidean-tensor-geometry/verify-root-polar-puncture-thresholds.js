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

const assert=require('node:assert/strict'), scale=2520n;
for(const n of [6,7,8]){
const I=Array.from({length:n},(_,i)=>i);
const E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:
  (i<n-1&&j<n-1&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===n-1)?-1n:0n));
const determinant=det(G);
const adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const roots=E.map(r=>r.slice()), index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){
  const r=reflect(roots[j],i);
  if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r);}
}
if(roots.length!==[72,126,240][n-6])throw Error("root count");
const positive=roots.filter(r=>r.every(v=>v>=0n));
const maximal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v>=r[i])));
const minimal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v<=r[i])));

function vertices(C){
  const U=maximal(positive.filter(r=>!C.includes(r))), L=minimal(C);
  
  if(I.some(i=>!U.some(r=>r[i]>0n)))throw Error('unbounded chamber coordinate');
  const rows=[...E,...U,...L], rhs=[...I.map(()=>0n),...U.map(()=>1n),...L.map(()=>1n)], out=new Map();
  function visit(set,start){
    if(set.length<n){
      for(let i=start;i<=rows.length-n+set.length;i++)visit([...set,i],i+1);
      return;
    }
    const a=set.map(i=>rows[i]),b=set.map(i=>rhs[i]);
    let d=det(a);if(!d)return;
    const N=I.map(j=>det(a.map((r,i)=>r.map((v,k)=>j===k?b[i]:v))));
    if(d<0n){d=-d;N.forEach((v,i)=>N[i]=-v);}
    if(N.some(v=>v<0n)||U.some(r=>dot(r,N)>d)||L.some(r=>dot(r,N)<d))return;
    if(N.some(v=>scale*v%d))throw Error("rescale");
    const w=N.map(v=>scale*v/d);out.set(w.join(),w);
  }
  visit([],0);return [...out.values()];
}
const norm=k=>dot(k,adj.map(row=>dot(row,k)));


const ds=scale*scale*determinant;let ideals=[[]],base=0n;
const tau=[3,4,6][n-6];let chamberExact=false;for(let k=0;k<=tau+1;k++){let count=0,fail=[];
 for(const a of ideals){const C=a.map(i=>positive[i]),V=vertices(C);count+=V.length;for(const v of V){
  const B=positive.filter(r=>dot(r,v)>scale);if(!B.length){if(norm(v)>base)base=norm(v);continue;}
  const bary=I.map(j=>scale*B.reduce((s,r)=>s+dot(G[j],r),0n));if(v.every((x,i)=>x*BigInt(B.length)===bary[i]))continue;
  const pr=B.map(r=>dot(r,v)),mh=pr.reduce((a,b)=>a>b?a:b);
  fail.push({B:B.length,y:v.map(x=>Number(x)/2520),q2:Number(norm(v))/Number(ds),root:Number(mh)/2520,sep:norm(v)*scale>mh*ds&&norm(v)>base});
 }}
 if(k<=tau){assert.equal(fail.length,0);}else{assert(fail.some(v=>v.sep));chamberExact=true;}
 console.log('chamber',n,k,'ideals',ideals.length,'vertices',count,'non-barycentric',fail.length);
 const next=new Map();for(const a of ideals)for(const r of maximal(positive.filter((_,i)=>!a.includes(i)))){const b=[...a,positive.indexOf(r)].sort((x,y)=>x-y);next.set(b.join(),b);}ideals=[...next.values()];
}assert(chamberExact);
function rank(A){if(!A.length)return 0;let n=0,B=A.map(v=>v.slice());for(let j=0;j<I.length;j++){const t=B.findIndex((row,i)=>i>=n&&row[j]!==0n);if(t<0)continue;[B[n],B[t]]=[B[t],B[n]];for(let k=n+1;k<B.length;k++){const b=B[k][j],a=B[n][j];if(!b)continue;B[k]=B[k].map((v,i)=>a*v-b*B[n][i]);}n++;if(n===B.length)break;}return n;}
const theta=maximal(positive)[0],F=[], gram=(a,b)=>dot(a,G.map(t=>dot(t,b)));
for(let mask=0;mask<(1<<n)-1;mask++){
 const f=positive.filter(r=>I.every(i=>r[i]===theta[i]||((mask>>i)&1))),d=rank(f.map(r=>r.map((v,i)=>v-theta[i])));if(d===1){assert.equal(f.length,2);assert.equal(gram(f[0],f[1]),1n);}if(f.length===d+1)continue;
 const cross=f.length===2*d&&f.every(r=>f.filter(s=>s!==r&&gram(r,s)!==1n).length===1&&f.filter(s=>s!==r&&gram(r,s)===0n).length===1);
 F.push({mask,d,v:f.length,cross});}
F.sort((a,b)=>a.d-b.d);assert.equal(F[0].d,tau+1);assert(F.some(f=>f.d===tau+1&&f.cross));console.log('faces',n,'first non-simplex:',F[0]);}

