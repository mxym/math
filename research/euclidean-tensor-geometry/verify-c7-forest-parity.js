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

const x=157n,y=350n, hiD=24n*y**4n, hiN=hiD-12n*x*x*y*y+x**4n;
assert(1841n*hiN<1659n*hiD,'upper theta cosine certificate');
assert(1659n**3n<49n*500n**3n,'theta below 7^(2/3)');
assert(1659n**248n<500n**248n*7n**153n,'pseudoforest integer ratio certificate');
const a=22n,b=49n, loD=720n*b**6n;
const loN=loD-360n*a*a*b**4n+30n*a**4n*b*b-a**6n;
assert(737n*loN>663n*loD,'lower theta cosine certificate');
assert(7n**8n*200n**13n<663n**13n,'pseudoforest strict theta gap');
