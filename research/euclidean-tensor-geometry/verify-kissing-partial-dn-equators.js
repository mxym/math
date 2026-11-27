'use strict';
// Run: node verify-kissing-partial-dn-equators.js (integer arithmetic).
// Coordinates u=2v. Entries of a D_n root are 0, +1, -1.
const assert=require('node:assert/strict');
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0), neg=a=>a.map(x=>-x);
for(const n of [5,6]){
  const I=Array.from({length:n},(_,i)=>i),R=[];
  for(const i of I)for(let j=0;j<i;j++)
    for(const a of [-1,1])for(const b of [-1,1]){
      const r=I.map(()=>0);r[i]=a;r[j]=b;R.push(r);
    }
  const ids=new Map(R.map((r,i)=>[r.join(','),i]));
  const at=a=>ids.get(a.join(',')),candidates=[];
  function grid(u){
    if(u.length<n){for(let t=-2;t<=2;t++)grid([...u,t]);return;}
    const blockers=R.map((r,i)=>dot(u,r)>2?i:-1).filter(i=>i>=0);
    if(blockers.length<=2)candidates.push({u,blockers,h2:8-dot(u,u)});
  }
  grid([]);
  const classes=new Set(),r=R[0],expected=n===5?[256,259,260,259,259,259]:[744,747,748,747,747,747],counts=[];
  for(let j=0;j<R.length;j++){
    const s=R[j],k=dot(r,s),t=r.filter((v,i)=>v&&s[i]).length,key=k+':'+t;
    if(classes.has(key))continue;classes.add(key);
    const U=candidates.filter(a=>a.blockers.every(i=>i===0||i===j));
    assert(U.every(a=>a.h2>=0));
    assert(U.filter(a=>a.h2===0).every(a=>at(a.u.map(c=>c/2))!==undefined));
    const M=new Set([0,j]),D=R.filter((x,i)=>!M.has(i)&&!M.has(at(neg(x))));
    for(const x of R)if(!D.includes(x)){
      // One reflection of present roots already supplies this missing root.
      assert(D.some(y=>{const z=x.map((v,i)=>v-y[i]);
        return D.includes(R[at(z)])&&dot(y,z)===-1;}));
    }
    let bad=0;
    for(const a of U)for(const b of U){
      const p=dot(a.u,b.u);
      if(p < -4 && a.h2*b.h2 < (p+4)**2)bad++;
    }
    assert.equal(bad,k===-2?10:0);
    const expectedCount=key==='2:2'?expected[0]:key==='1:1'?expected[2]:expected[1];
    assert.equal(U.length,expectedCount);
    counts.push([key,U.length,bad]);
  }
  assert.equal(classes.size,6);
  console.log('D'+n+' [dot:common support, half-grid points, ordered sub-threshold pairs]',counts);
}
