/* Node 18+. Toy-field arithmetic only; no security or protocol data. */
'use strict';
let exact=0,numeric=0;
function ex(q,m){++exact;if(!q)throw Error(m);}
function nu(q,m){++numeric;if(!q)throw Error(m);}
function determinant(a) {
  a=a.map(r=>r.map(BigInt));const n=a.length;
  let sign=1n, prev=1n;
  for(let k=0;k<n-1;++k){
    let p=k;while(p<n&&a[p][k]===0n)++p;
    if(p===n)return 0n;
    if(p!==k){[a[k],a[p]]=[a[p],a[k]];sign=-sign;}
    const v=a[k][k];
    for(let i=k+1;i<n;++i)for(let j=k+1;j<n;++j) {
      const w=v*a[i][j]-a[i][k]*a[k][j];
      ex(w%prev===0n,'exact Bareiss elimination');
      a[i][j]=w/prev;
    }
    for(let i=k+1;i<n;++i)a[i][k]=0n;
    prev=v;
  }
  return sign*a[n-1][n-1];
}
function mulMat(a){
  const d=a.length;
  return Array.from({length:d},(_,i)=>Array.from({length:d},(_,j)=>{
    const k=i-j;
    return k>=0?a[k]:-a[d+k];
  }));
}
let seed=26037201;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>10)%n;}
for(const d of [2,4,8])for(let k=0;k<384;++k){
  const a=Array.from({length:d},()=>rng(19)-9);if(a.every(x=>x===0))a[0]=1;
  const M=mulMat(a);
  ex(determinant(M)!==0n,'multiplication by a nonzero field scalar is injective');
  let energy=0;
  for(let j=0;j<d/2;++j){
    const at=Math.PI*(2*j+1)/d;
    const x=a.reduce((s,t,i)=>s+t*Math.cos(i*at),0);
    const y=a.reduce((s,t,i)=>s+t*Math.sin(i*at),0);
    energy+=2*(x*x+y*y);
  }
  nu(Math.abs(energy-d*a.reduce((s,t)=>s+t*t,0))<1e-11,'canonical norm');
}
for(let t=8n;t<=512n;++t) {
  const s=8n,d=4n;
  const detS=t*t*s*s,covol=d**(d/2n);
  ex(detS===64n*t*t && covol===16n,'complex-place widening determinant vs fixed covolume');
  ex(detS>=s**4n,'widening keeps the smallest width fixed');
}
console.log('anisotropic kernel normalization:',exact,'exact checks;',numeric,'deterministic numeric checks');
