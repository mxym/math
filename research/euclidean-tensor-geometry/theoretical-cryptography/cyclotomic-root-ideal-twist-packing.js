'use strict';
// Audit only definite Euclidean forms on abstract arrays and modular character arithmetic.
const assert=(b,m)=>{if(!b)throw Error(m);};
const range=n=>Array.from({length:n},(_,i)=>i);
const gcd=(a,b)=>b?gcd(b,a%b):a;
function pow(a,n,q){let p=1;for(;n;n=Math.floor(n/2),a=a*a%q)if(n%2)p=p*a%q;return p;}
const primes=range(10000).filter(n=>n>=2&&!range(Math.floor(Math.sqrt(n))+1).slice(2).some(p=>n%p===0));
let exact=0,numerical=0,maxErr=0;
for(const p of primes.filter(p=>p>2&&p<100)){
 const q=primes.find(q=>q%p===1);
 const z=range(q).slice(2).map(a=>pow(a,(q-1)/p,q)).find(a=>a!==1);
 const h=(p-1)/2;
 const A=range(h).map(i=>range(h).map(j=>{
   let r=((i+1)*(j+1))%p;
   return (2+2*q-pow(z,r,q)-pow(z,p-r,q))%q;
 }));
 for(let i=0;i<h;i++){
   const j=A.findIndex((v,j)=>j>=i&&v[i]!==0);
   assert(j>=0,'even Fourier orbit full rank');exact++;
   [A[i],A[j]]=[A[j],A[i]];
   let v=pow(A[i][i],q-2,q);
   for(let j=i+1;j<h;j++){let b=v*A[j][i]%q;for(let k=i;k<h;k++)A[j][k]=(A[j][k]+q*q-b*A[i][k])%q;}
 }
}
for(const D of [[3],[5],[3,3],[3,4],[3,3,3]]){
 const W=D.map(x=>x-1);
 const nu=W.reduce((x,y)=>x*y,1),n=D.reduce((x,y)=>x*y,1);
 const index=(L,a)=>a.reduce((v,x,j)=>v*L[j]+x,0);
 function coords(L){let E=[[]];for(const d of L)E=E.flatMap(x=>range(d).map(p=>[...x,p]));return E;}
 const Bs=coords(D).map(id=>coords(W).map(j=>id.reduce((z,x,a)=>z*(x===W[a]?-1:x===j[a]?1:0),1)));
 let low=Infinity,second=Infinity;
 for(let i=1;i<3**nu;i++){
   let j=i,V=range(nu).map(()=>{let v=j%3;j=Math.floor(j/3);return v===2?-1:v;});
   let Z=Bs.map(a=>a.reduce((s,x,j)=>s+x*V[j],0));
   let v=Z.reduce((a,b)=>a+b*b,0),m=2**D.length;
   if(v===m){assert(Z.every(x=>Math.abs(x)<=1),'unit entries at minimum');for(let a=0;a<D.length;a++){let S=new Set(coords(D).filter((x,i)=>Z[i]!==0).map(x=>x[a]));assert(S.size===2,'box support');exact++;}}
   assert(v>=m,'squared minimum');exact++;
   low=Math.min(low,v);if(v>m)second=Math.min(second,v);
 }
 assert(low===2**D.length&&second===(D.length>1?3*2**(D.length-1):D[0]===3?6:4),'initial shells');exact++;
}
for(const N of [3,4,5,7,8,9,12,15,16,21,25,27,32,35,36,45,60,63,75,84,105,225,315]){
 const p=primes.filter(p=>p%2&&N%p===0),B=p.reduce((a,p)=>a*(p-1)/2,1);
 const G=range(Math.ceil(N/2)).filter(g=>g>0&&gcd(g,N)===1);
 const key=g=>p.map(q=>Math.min(g%q,q-g%q)).join(',');
 const cells={};
 for(let i=0;i<G.length;i++){let k=key(G[i]);(cells[k]??=[]).push(i);}
 const H=Object.values(cells),D=G.length/B;
 assert(H.length===B&&H.every(c=>c.length===D),'uniform residue fibers');exact++;
 for(const t of [.001,.037,.18,Math.log(2)/2,Math.log(3)/2]){
   let a=new Float64Array(G.length);
   for(const cell of H)for(let j=0;j<cell.length;j++)a[cell[j]]=j<Math.floor(D/2)?t:j>=D-Math.floor(D/2)?-t:0;
   let sum=Array.from(a).reduce((x,y)=>x+y,0);
   assert(Math.abs(sum)<2e-14,'balanced log weights');numerical++;
   const expected=D%2?((D-1)*Math.cosh(t)+1)/D:Math.cosh(t);
   const reps=H.map(c=>G[c[0]]);
   for(const v of reps){
     let W=G.map(g=>p.reduce((z,p)=>z*(2-2*Math.cos(2*Math.PI*(v*g%p)/p)),1));
     let baseline=W.reduce((z,w)=>z+w,0),E=W.reduce((z,w,j)=>z+w*Math.exp(a[j]),0)/baseline;
     assert(Math.abs(E-expected)<1e-13,'all first-shell energies');numerical++;
     maxErr=Math.max(maxErr,Math.abs(E-expected));
   }
 }
}
console.log(JSON.stringify({exact,numerical,maxErr}));
