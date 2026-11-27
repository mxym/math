'use strict';
const maximum=n=>Math.max(2*n-2,Math.min(n,7)*(Math.min(n,7)-1)/2);
const audit=[];let residue=0;
for(let n=4;n<=12;n++){let over=0,match=0,bic=0,dual=0;for(let m=0;m<1<<(n-1);m++){
 const adj=Array.from({length:n},()=>[]),E=[];
 for(let j=1;j<n;j++)if(m>>(j-1)&1)for(let i=0;i<j;i++){E.push([i,j]);adj[i].push(j);adj[j].push(i);}
 if(E.length<=maximum(n))continue;over++;
 function matching(V,k){if(!k)return true;if(V.length<2*k)return false;const i=V[0];for(const j of adj[i])if(V.includes(j)&&matching(V.filter(v=>v!==i&&v!==j),k-1))return true;return matching(V.slice(1),k);}
 if(matching(Array.from({length:n},(_,i)=>i),4)){match++;continue;}
 let K=false;for(let a=0;a<n;a++)for(let b=0;b<a;b++)for(let c=0;c<b;c++)if(adj[a].filter(i=>adj[b].includes(i)&&adj[c].includes(i)).length>=6)K=true;
 if(K){bic++;continue;}
 // Propose nonnegative weights; only the BigInt Cauchy certificate below is trusted.
 const r=E.map(()=>0),v=Array(n).fill(0);for(let t=0;t<500;t++)for(const [j,[a,b]] of E.entries()){
   const d=Math.max(-r[j],(1-v[a]-v[b])/2);r[j]+=d;v[a]+=d;v[b]+=d;
 }
 const z=r.map(x=>BigInt(Math.round(10000*x))),s=z.reduce((a,b)=>a+b,0n),u=Array(n).fill(0n);
 if(z.some(x=>x<0n)||s===0n)throw Error('invalid weight');for(const [j,[a,b]] of E.entries()){u[a]+=z[j];u[b]+=z[j];}
 if(s*s<2n*u.reduce((a,x)=>a+x*x,0n))throw Error('no exact dual certificate');
 dual++;residue++;
 }audit.push([n,over,match,bic,dual]);}
if(residue!==24)throw Error('census');console.log('n, over, four disjoint edges, K3,6, exact dual:',audit);
