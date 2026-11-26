'use strict';
// Exact integer-rational endpoint comparator; products in this census fit in safe integers.

const hits=[];
let scanned=0;
const cmp=(an,ad,bn,bd)=>an*bd-bn*ad;
function bounds(n,w){
 const d=n*w, out=[];
 for(let j=0;j<=w;j++)out.push([Math.max(0,n*j-1),Math.min(d,n*j+1),d]);
 return out;
}
for(let n=5;n<=10;n++){
 const U=Math.floor(8*(n-2)/(n-4)),V=2*(n-1)*U;
 const cache=Array.from({length:V+1},(_,w)=>w?bounds(n,w):[]);
 for(let r=2;r<n;r++){
  const core=Array.from({length:n-2},(_,i)=>i+2).filter(w=>w!==r).flatMap(w=>cache[w]);
  for(let u=n;u<=U;u++)for(let v=u+1;v<=2*(n-1)*u;v++){
   scanned++;
   const a=core.concat(cache[u],cache[v]);
   a.sort((p,q)=>cmp(p[0],p[2],q[0],q[2]));
   let x=0,d=1;
   for(const [l,h,e] of a){
    if(cmp(l,e,x,d)>0)break;
    if(cmp(h,e,x,d)>0){x=h;d=e;}
    if(x===d){hits.push([n,r,u,v]);break;}
   }
  }
 }
}
if(scanned!==22706||JSON.stringify(hits)!=="[[5,3,6,8]]")throw Error(JSON.stringify({scanned,hits}));
(typeof console==="undefined"?text:console.log)({scanned,hits});