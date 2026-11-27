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
const gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));
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


const W=[[0,1,0,0,0,0],[7,17,0,7,2,0],[1,0,1,0,1,0],[23,6,23,0,23,0],[0,1,0,1,0,0],[1,0,0,0,1,1],[20,29,0,0,21,20],[1,0,1,0,0,0],[12,10,9,12,10,0],[1,0,0,0,1,0],[21,20,3,0,21,0],[13,0,8,0,5,16],[9,12,0,11,9,9],[18,0,19,18,0,8],[93,0,17,0,40,0],[25,16,0,25,16,0],[2,0,0,1,0,1],[11,0,5,7,6,6],[16,0,33,0,17,20],[41,0,0,15,10,10],[25,0,12,12,13,1],[1,0,0,0,0,1],[1,0,0,1,0,1],[1,0,1,0,1,1],[0,0,1,0,0,0],[2,0,0,1,0,0],[41,0,0,0,17,13],[11,3,0,9,2,2],[27,0,0,4,0,4],[1,0,0,1,0,0],[82,0,25,0,0,0],[41,18,0,0,0,0],[1,0,0,0,0,0]].map(v=>v.map(BigInt)),real=new Map();function exactMask(w){const q=norm(w);if(q<=0n||positive.some(r=>dot(r,w)>0n&&determinant*dot(r,w)**2n===2n*q))return null;return positive.filter(r=>dot(r,w)>0n&&2n*determinant*dot(r,w)**2n>q);}
const canon=C=>{const u=lab(C),v=lab(C.map(reverse));return u<v?u:v;};for(const w of W){const C=exactMask(w);if(!C||real.has(canon(C)))throw Error('duplicate or root witness');real.set(canon(C),w);}
let cur=[[]],form=0,bad=0,missing=0,hist=[];for(let k=1;k<=16;k++){
 const next=new Map();for(const S of cur)for(const r of maximal(positive.filter((_,i)=>!S.includes(i)))){const D=S.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(D.join(),D);}cur=[...next.values()];
 if(k<5)continue;const seen=new Set();let good=0,count=0,geom=0,impossible=0;
 for(const S of cur){const C=S.map(i=>positive[i]),y=canon(C);if(seen.has(y))continue;seen.add(y);form++;
 if(real.has(y)){const z=orbit(getMask(C)).length;count+=z;good++;continue;}
 if(lower(C)){bad++;impossible++;continue;}
 const vs=vertices(C),q=2n*determinant*144n;if(!vs.length||!vs.every(w=>norm(w)<q||norm(w)===q&&(!exactMask(w)||lab(exactMask(w))!==lab(C))))throw Error('unclassified');
 missing++;geom++;
 }hist.push([k,cur.length,seen.size,good,count,impossible,geom]);}
const expected=[[5,3,2,1,432,0,1],[6,3,2,2,15120,0,0],[7,4,3,3,30240,0,0],[8,6,4,4,47790,0,0],[9,7,4,4,69120,0,0],[10,8,5,5,88560,0,0],[11,10,6,6,66384,0,0],[12,12,7,3,23760,4,0],[13,14,8,2,10800,6,0],[14,16,9,1,4320,8,0],[15,19,11,1,864,10,0],[16,22,13,1,54,12,0]];
if(JSON.stringify(hist)!==JSON.stringify(expected)||hist.reduce((s,r)=>s+r[4],0)!==357444)throw Error('signed orbit counts');
if(real.size!==33||form!==74||bad!==40||missing!==1)throw Error('census');console.log(JSON.stringify(hist));console.log('absolute number of signed patterns',hist.reduce((s,r)=>s+r[4],0));