'use strict';
// Small exact checks of identities for integral negacyclic matrices. No sampled data.
let checks=0;function assert(x){checks++;if(!x)throw Error('identity failed');}
const eq=(a,b)=>a.length===b.length&&a.every((v,i)=>v===b[i]);
for(const d of [4,8,16,32]){
 const h=d/4,I=Array.from({length:d},(_,i)=>i),unit=i=>I.map(j=>BigInt(i===j));
 const shift=(x,a)=>I.map(i=>{const k=i-a;return k<0?-x[k+d]:x[k];});
 const A=x=>shift(x,h).map((v,i)=>v-shift(x,3*h)[i]);
 const M=x=>x.map((v,i)=>v+A(x)[i]),mInv=x=>A(x).map((v,i)=>v-x[i]);
 for(const j of I){
  const e=unit(j),a=A(e);assert(eq(A(a),e.map(v=>2n*v)));assert(eq(M(mInv(e)),e));
  assert(a[j]===0n);assert(a.filter(x=>x!==0n).length===2);
  for(const i of I){
    assert(a[i]===A(unit(i))[j]);assert(a[i]===0n||i%h===j%h);
    if(i!==j)assert(a[i]*a[i]<2n); // All two-coordinate principal expanding projectors positive.
  }
  let v=unit((j+2*h)%d);
  for(let n=0;n<15;n++){assert(v[j]===0n);v=mInv(v);}
 }
}
console.log({exactMatrixChecks:checks});