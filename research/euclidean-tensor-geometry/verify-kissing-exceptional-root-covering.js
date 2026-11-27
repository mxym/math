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
function chamberCertificate(n, multiplicity, idealSize, expectedRoots, expectedIdeals, witness, equalityDivisor) {
  const idx=Array.from({length:n},(_,i)=>i);
  const unit=idx.map(i=>idx.map(j=>BigInt(i===j)));
  const g=idx.map(i=>idx.map(j=>i===j?2n:
    i<n-1&&j<n-1&&Math.abs(i-j)===1 || Math.min(i,j)===2&&Math.max(i,j)===n-1 ? -1n:0n));
  const gdet=det(g);
  const adj=idx.map(i=>idx.map(j=>(i+j)%2===0?
    det(g.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i))):
    -det(g.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
  const roots=unit.map(row=>row.slice()), seen=new Set(roots.map(row=>row.join(',')));
  for(let h=0;h<roots.length;h++)for(const i of idx){
    const r=roots[h].slice();
    r[i]-=dot(g[i],r);
    const key=r.join(',');
    if(!seen.has(key)){seen.add(key);roots.push(r);}
  }
  if(roots.length!==expectedRoots || roots.some(r=>dot(r,g.map(row=>dot(row,r)))!==2n))throw Error('root count');
  const positive=roots.filter(r=>r.every(v=>v>=0n));
  const maximal=list=>list.filter(r=>!list.some(s=>s!==r&&s.every((x,i)=>x>=r[i])));
  const highest=maximal(positive);
  if(highest.length!==1)throw Error('highest root');
  const rootWeights=g.map(row=>dot(row,highest[0]));
  if(rootWeights.some(v=>v<0n))throw Error('highest root chamber');
  const complement=s=>positive.filter((_,i)=>!s.includes(i));
  let ideals=[[]];
  for(let k=0;k<idealSize;k++){
    const next=new Map();
    for(const removed of ideals)for(const r of maximal(complement(removed))){
      const ind=[...removed,positive.indexOf(r)].sort((a,b)=>a-b);
      next.set(ind.join(','),ind);
    }
    ideals=[...next.values()];
  }
  if(ideals.length!==expectedIdeals)throw Error('ideal count');
  let checked=0, atRoot=0, atExtra=0;
  const w=idx.map(i=>BigInt(witness.includes(i)));
  for(const removed of ideals){
    const inequalities=maximal(complement(removed));
    if(idx.some(i=>!inequalities.some(row=>row[i]>0n)))throw Error('unbounded chamber');
    const matrix=[...unit,...inequalities], selected=[];
    function scan(start){
      if(selected.length<n){
        for(let j=start;j<=matrix.length-n+selected.length;j++){
          selected.push(j);
          scan(j+1);
          selected.pop();
        }
        return;
      }
      const rows=selected.map(i=>matrix[i]), rhs=selected.map(i=>BigInt(i>=n));
      let denominator=det(rows);
      if(!denominator)return;
      const numerator=idx.map(j=>det(rows.map((row,i)=>row.map((v,k)=>j===k?rhs[i]:v))));
      if(denominator<0n){
        denominator=-denominator;
        numerator.forEach((v,i)=>numerator[i]=-v);
      }
      if(numerator.some(x=>x<0n)||inequalities.some(r=>dot(r,numerator)>denominator))return;
      checked++;
      const normNumerator=dot(numerator,adj.map(row=>dot(row,numerator)));
      const limit=2n*gdet*denominator*denominator;
      if(normNumerator>limit)throw Error('chamber norm bound');
      if(normNumerator===limit){
        if(numerator.every((x,i)=>x===denominator*rootWeights[i])) atRoot++;
        else if(equalityDivisor && numerator.every((x,i)=>x*BigInt(equalityDivisor)===denominator*w[i])) atExtra++;
        else throw Error('nonroot equality');
      }
    }
    scan(0);
  }
  const numerator=dot(w,adj.map(row=>dot(row,w)));
  const strict=positive.filter(r=>2n*gdet*dot(r,w)**2n>numerator);
  if(strict.length!==multiplicity)throw Error('sharp witness');
  return {n,roots:roots.length,ideals:ideals.length,checked,atRoot,atExtra,strict:strict.length};
}
const results = [
  chamberCertificate(6,5,4,72,2,[1],0),
  chamberCertificate(7,6,5,126,2,[5,6],0),
  chamberCertificate(7,6,6,126,2,[5,6],2),
  chamberCertificate(8,8,7,240,2,[7],0),
  chamberCertificate(8,8,8,240,2,[7],2),
];
const expected = [[42,10,0],[34,6,0],[50,10,1],[40,6,0],[37,5,1]];
if (results.some((r,i)=>[r.checked,r.atRoot,r.atExtra].join(",")!==expected[i].join(","))) {
  throw Error("unexpected vertex counts");
}
console.log(results);


function checkComplementaryE6Blockers(){
 const I=[0,1,2,3,4,5];
 const G=I.map(i=>I.map(j=>i===j?2n:((i<5&&j<5&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===5))?-1n:0n));
 const roots=I.map(i=>I.map(j=>BigInt(i===j))),seen=new Set(roots.map(r=>r.join()));
 for(let k=0;k<roots.length;k++)for(const i of I){
  const r=roots[k].slice();r[i]-=dot(G[i],r);
  const s=r.join();if(!seen.has(s)){seen.add(s);roots.push(r)}
 }
 const x=[49,98,126,88,50,66].map(BigInt), y=[-37,-74,-111,-112,-113,-36].map(BigInt);
 const gx=G.map(r=>dot(r,x)),gy=G.map(r=>dot(r,y));
 const nx=dot(x,gx),ny=dot(y,gy),xy=dot(x,gy);
 if(roots.length!==72||nx!==3054n||ny!==11478n||xy!==-3126n||4n*xy*xy<=nx*ny)throw Error('norm or dot');
 const blockers=(v,N)=>roots.filter(r=>{const s=dot(r,v);return s>0n&&2n*s*s>N});
 const a=blockers(gx,nx),b=blockers(gy,ny);
 const axis=r=>r.every(t=>t>=0n)?r.join():r.map(t=>-t).join();
 if(a.length!==5||b.length!==5||new Set([...a,...b].map(axis)).size!==10)throw Error('blocker axes');
 console.log({rank:6,blockerCounts:[a.length,b.length],distinctAxes:10,partialCodeSize:64});
}
checkComplementaryE6Blockers();
