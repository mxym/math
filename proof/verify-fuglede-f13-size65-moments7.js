'use strict';
// Every noncollinear six-point subset of F_13^2 determines >=5 slopes.
const p=13, mod=x=>(x%p+p)%p;
const inv=Array.from({length:p},(_,u)=>Array.from({length:p},(_,v)=>v).find(v=>mod(u*v)===1));
const pts=Array.from({length:p*p},(_,i)=>[i%p,Math.floor(i/p)]);
const slope=(a,b)=>{const [x,y]=pts[a],[u,v]=pts[b];return a===b?-1:x===u?p:mod((y-v)*inv[mod(x-u)]);};
const D=pts.map((_,i)=>pts.map((_,j)=>slope(i,j))), T=[0,1,p];
let masks=0,triples=0;
for(let s=1;s<=p-2;s++){
  const M=new Set([0,p-1,p,s]); masks++;
  const C=pts.map((_,i)=>i).filter(i=>T.every(j=>M.has(D[i][j])));
  for(let i=0;i<C.length;i++)for(let j=i+1;j<C.length;j++)for(let k=j+1;k<C.length;k++){
    triples++;
    if(M.has(D[C[i]][C[j]])&&M.has(D[C[i]][C[k]])&&M.has(D[C[j]][C[k]]))throw Error('six-site example');
  }
}
console.log({masks,triples});
