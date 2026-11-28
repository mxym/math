// Usage: node verify_factor_moran_high_fitness_star.mjs
"use strict";
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a;}
function R(a,b=1n){a=BigInt(a);b=BigInt(b);if(!b)throw Error("denominator");let g=gcd(a,b);if(b<0n)g=-g;return [a/g,b/g];}
const sum=(a,b)=>R(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const sub=(a,b)=>sum(a,[-b[0],b[1]]);
const mul=(a,b)=>R(a[0]*b[0],a[1]*b[1]);
const div=(a,b)=>R(a[0]*b[1],a[1]*b[0]);
const less=(a,b)=>a[0]*b[1]<b[0]*a[1];
const zero=R(0),one=R(1),two=R(2);
function val(G){
 const n=G.length, d=G.map(A=>R(1,A.length));
 const t=G.map(A=>A.reduce((a,u)=>sum(a,d[u]),zero));
 let s=zero;
 for(let u=0;u<n;u++){
  s=sub(s,mul(t[u],t[u]));
  for(const v of G[u]){
   if(u>=v)continue;
   const cut=sub(two,sum(d[u],d[v]));
   const down=sum(mul(sub(t[u],d[v]),t[v]),mul(sub(t[v],d[u]),t[u]));
   s=sum(s,mul(sum(d[u],d[v]),div(down,cut)));
  }
 }
 return div(s,R(n));
}
function small(n){
 const L=[];
 for(let j=0;j<n;j++)for(let i=0;i<j;i++)L.push([i,j]);
 const k=n-1, star=div(sub(sub(R(n),R(k*k)),R(1,k)),R(n));
 let connected=0,stars=0,gap=null,attain=0,witness=null;
 for(let mask=0;mask<1<<L.length;mask++){
  const G=Array.from({length:n},()=>[]);
  for(let k=0;k<L.length;k++)if(mask>>k&1){const [u,v]=L[k];G[u].push(v);G[v].push(u);}
  if(G.some(a=>!a.length))continue;
  const V=[0]; for(let k=0;k<V.length;k++)for(const w of G[V[k]])if(!V.includes(w))V.push(w);
  if(V.length!==n)continue;connected++;
  const g=sub(val(G),star);
  if(G.some(a=>a.length===k)&&G.filter(a=>a.length===1).length===k){stars++;if(g[0])throw Error("star coefficient");continue;}
  if(!gap||less(g,gap)){gap=g;attain=1;witness=G;}
  else if(g[0]===gap[0]&&g[1]===gap[1])attain++;
 }
 if(!gap||gap[0]<=0n||stars!==n)throw Error("nonpositive gap or wrong star count");
 return {n,connected,stars,star:star.join("/"),gap:gap.join("/"),attain,witness};
}
for(const n of [3,4,5,6])console.log(JSON.stringify(small(n)));
