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

const n=7,I=Array.from({length:n},(_,i)=>i),E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:((i<6&&j<6&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===6))?-1n:0n));
const roots=E.slice(),index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){const r=reflect(roots[j],i);if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r)}}
const C=roots.flatMap((r,i)=>r[5]+r[6]>2n?[i]:[]);
const neg=roots.map(r=>index.get(r.map(v=>-v).join()));
const mask=xs=>xs.reduce((m,i)=>m|(1n<<BigInt(i)),0n);
const perm=I.map(i=>roots.map(r=>index.get(reflect(r,i).join())));

const D=det(G), adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const base=adj.map(r=>r[5]+r[6]), q=[base], seen=new Set(q.map(v=>v.join()));
for(let i=0;i<q.length;i++)for(const k of I){const p=reflect(q[i],k),key=p.join();if(!seen.has(key)){seen.add(key);q.push(p);}}
const g0=G.map(r=>dot(r,base)), gdot=(p,r)=>dot(G.map(row=>dot(row,p)),r);
const orbit=q.map(v=>({v,b:mask(roots.flatMap((r,i)=>gdot(v,r)>2n*D?[i]:[]))}));
if(roots.length!==126 || C.length!==6 || dot(g0,base)!==8n*D*D)throw Error('E7 witness norm');
const baseMask=mask(C), axes=mask([...C,...C.map(i=>neg[i])]);
const masks=[...new Set(orbit.map(o=>o.b))];
const by={};const posPairs=[];
for(const o of orbit){
 if(o.b&axes)continue;
 const ip=dot(g0,o.v);
 if(ip>=-4n*D*D)continue;
 const U=o.b|baseMask, k=masks.filter(b=>(U&b)===b).length;
 by[k]=(by[k]??0)+1;
 posPairs.push({k,ip:Number(ip),union:U.toString(),v:o.v.map(Number)});
}
if(q.length!==4032||masks.length!==4032||posPairs.length!==20||by[2]!==20||Object.keys(by).length!==1)throw Error('E7 orbit census');
return {count:q.length,signedMasks:masks.length,negative:by};
})();
console.log(summary);
