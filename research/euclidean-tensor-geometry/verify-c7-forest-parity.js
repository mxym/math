'use strict';
// Independent finite checks for the analytic forest parity proof.
const assert=(v,m)=>{if(!v)throw Error(m)};

const mod=x=>(x%7+7)%7;
const sy=[0,1,2,3,3,2,1];
const vs=[0,1,2,3,4,5,6];
const bits=[...Array(8)].map((_,i)=>vs.filter(x=>x===0||i&(1<<(sy[x]-1))));
const bit=x=>x===0?0:1<<(sy[x]-1);
const mask=S=>S.reduce((a,x)=>a|bit(x),0);
function union(a,b){
 if(a&b)return -1;
 return mask(bits[a].flatMap(x=>bits[b].map(y=>mod(x+y))));
}
const C=Array.from({length:18},(_,i)=>[(i/6|0)+1,i%6+1]); // canonical signs child 1,2,3.
const edges=Array.from({length:8},()=>Array.from({length:8},()=>null));
function dfs(S,D,start){
 if(D.length){
  for(let s=0;s<8;s++){
   if(S.some(([x,y])=>!y && x && (s&bit(x))))continue;
   const t=mask(S.filter(([x])=>!x || (s&bit(x))).map(([,y])=>y));
   if(!edges[s][t]||edges[s][t].D.length<D.length)edges[s][t]={D};
  }
 }
 if(D.length===5)return;
 for(let i=start;i<C.length;i++){
   const [a,b]=C[i];if(S.some(([x,y])=>x===a&&y===b))continue;
   const L=[];
   const seen=new Uint8Array(49);
   for(let s of [-1,0,1])for(const [x,y] of S){
    const xx=mod(x+s*a),yy=mod(y+s*b),z=xx+7*yy;
    if(!seen[z]){L.push([xx,yy]);seen[z]=1}
   }
   dfs(L,[...D,C[i]],i+1);
 }
}
dfs([[0,0]],[],0);

const size=[0,1,1,2,1,2,2,3];
const th=[[2,3,4,5],[1,2,3,4],[1,2,2,3],[0,1,1,2]];
const p=[-5,-3,-2,0],q=[0,2,3,5];
for(let s=0;s<8;s++)for(let t=0;t<8;t++)if(edges[s][t]){
 const n=edges[s][t].D.length;
 assert(n<=th[size[s]][size[t]],'local theta bound');
 assert(p[size[s]]+2*n<=q[size[t]],'transfer potential');
}
let branch=0;
for(let a=1;a<8;a++)for(let b=a;b<8;b++)if(!(a&b)){
 let u=union(a,b);assert(u===7,'non-full disjoint sum');
 assert(q[size[a]]+q[size[b]]-5<=p[3],'branch potential');branch++;
}
function binarySum(V,d){
 const N=Array.from({length:d},()=>0);
 let S=[N];
 for(const v of V)S=S.concat(S.map(x=>x.map((a,i)=>mod(a+v[i]))));
 assert(new Set(S.map(x=>x.join(','))).size===S.length,'lower block collision');
 return S.length;
}
const blocks=[binarySum([[1]],1),binarySum([[1],[2]],1),binarySum([[1,0],[0,1],[2,1],[4,1],[1,3]],2)];
const actual=Array.from({length:4},()=>Array(4).fill('-'));
for(let s=0;s<8;s++)for(let t=0;t<8;t++)if(edges[s][t]){
 let a=size[s],b=size[t],n=edges[s][t].D.length;
 if(actual[a][b]==='-'||n>actual[a][b])actual[a][b]=n;
}
(typeof console==='undefined'?text:console.log)({actualEdgeTransitions:actual,branchMasks:branch,binaryBlockSubsetSums:blocks});
