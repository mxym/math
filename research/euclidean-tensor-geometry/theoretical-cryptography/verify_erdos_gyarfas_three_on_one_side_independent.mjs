// Independent finite checks for the one-sided abelian quotient reduction.
// Usage: node verify_erdos_gyarfas_three_on_one_side_independent.mjs
"use strict";
const require=(ok,msg)=>{if(!ok)throw Error(msg)};
const range=n=>Array.from({length:n},(_,i)=>i);
const cols=m=>{
 const ans=[];
 function gen(x){
  if(x.length===m){if(x.reduce((a,b)=>a+b,0)>=3&&x.filter(y=>y===2).length<=1)ans.push(x);return;}
  for(let k=0;k<=2;k++)gen([...x,k]);
 }
 gen([]);return ans;
};
const pairs=m=>range(m).flatMap(i=>range(i).map(j=>[j,i]));
function* perm(x){
 if(x.length===0){yield [];return;}
 for(let j=0;j<x.length;j++)for(const z of perm(x.filter((_,i)=>i!==j)))yield [x[j],...z];
}
function quotientMultisets(m,n,cap,forceSum3=false){
 const C=cols(m).filter(c=>!forceSum3||c.reduce((a,b)=>a+b,0)===3),P=pairs(m),ans=[];
 function gen(start,stack,doubled,use,bound){
  if(stack.length===n){
   if(range(m).every(i=>stack.reduce((a,c)=>a+c[i],0)>=3))ans.push(stack);
   return;
  }
  for(let j=start;j<C.length;j++){
   const c=C[j],d=c.indexOf(2);
   if(d!==-1&&doubled.includes(d))continue;
   const u=[...use],v=[...bound];
   let okay=true;
   for(let p=0;cap&&p<P.length;p++){
    const [a,b]=P[p];if(!c[a]||!c[b])continue;
    u[p]++;
    if(d===a||d===b)v[p]=2;
    if(u[p]>v[p]){okay=false;break;}
   }
   if(okay)gen(j,[...stack,c],d<0?doubled:[...doubled,d],u,v);
  }
 }
 gen(0,[],[],Array(P.length).fill(0),Array(P.length).fill(3));
 return ans;
}
function orbitKey(C){
 return [...perm(range(C[0].length))].map(p=>C.map(c=>p.map(i=>c[i]).join("")).sort().join("/")).sort()[0];
}
function numberOfColumnLabelings(C){
 const q=new Map();
 for(const c of C){const k=c.join("");q.set(k,(q.get(k)||0)+1);}
 return [...q.values()].reduce((x,k)=>x/range(k).reduce((a,j)=>a*(j+1),1),24);
}
const tally={};
for(const C of quotientMultisets(3,4,false,true)){
 const key=orbitKey(C);tally[key]=(tally[key]||0)+numberOfColumnLabelings(C);
}
const orbitSizes=Object.values(tally).sort((a,b)=>a-b);
require(orbitSizes.join()==="1,24,36,48,72,144","capped 3-by-4 orbit sizes");
for(const n of [5,6,7])require(quotientMultisets(3,n,true).length===0,"three-row bound");
const seven=quotientMultisets(4,7,true);
require(seven.length===24,"four-row seven-column count");
require(new Set(seven.map(orbitKey)).size===2,"seven-column type count");
for(const C of seven){
 require(C.some(a=>a.filter(x=>x>0).length===2&&a.includes(2)&&C.some(b=>
     b!==a&&b.filter(x=>x>0).length===2&&b.indexOf(2)===a.indexOf(1)&&b.indexOf(1)===a.indexOf(2))),
     "seven-column template has no mirror");
}
require(quotientMultisets(4,8,true).length===0,"four-row eight-column bound");

// Check graph adjacency by literal DFS, without assuming the prescribed words.
function abelian(dims){
 const n=dims.reduce((a,b)=>a*b,1);
 const parts=range(n).map(x=>dims.map(d=>{const y=x%d;x=Math.floor(x/d);return y;}));
 function coord(x,y,sgn){
  let out=0,radix=1;
  for(let k=0;k<dims.length;k++){
   const d=dims[k],z=(parts[x][k]+sgn*parts[y][k]+d)%d;
   out+=radix*z;radix*=d;
  }
  return out;
 }
 return {n,add:(x,y)=>coord(x,y,1),sub:(x,y)=>coord(x,y,-1)};
}
function literalCycle(ops,a,b,c,d,shared){
 const {n,add,sub}=ops;
 const mids=[2,3,shared?2:4,5],off=[a,b,c,d];
 // Gauge each V leg independently, while requiring the shared V matching.
 const vshift=[1%n,2%n,shared?1%n:3%n,4%n];
 const adj=range(6*n).map(()=>new Set());
 function edge(x,y){adj[x].add(y);adj[y].add(x);}
 for(let j=0;j<4;j++)for(let x=0;x<n;x++){
  const mid=add(x,sub(off[j],vshift[j]));
  edge(x,mids[j]*n+mid);
  edge(mids[j]*n+x,n+add(x,vshift[j]));
 }
 const seen=new Set([0]);
 for(const len of [4,8,16]){
  function dfs(v,k){
   if(k===len-1)return adj[v].has(0);
   for(const w of adj[v]){
    if(seen.has(w))continue;
    seen.add(w);if(dfs(w,k+1))return true;seen.delete(w);
   }
   return false;
  }
  if(dfs(0,0))return len;
 }
 throw Error("literal graph has no cycle");
}
let total=0;const hist={4:0,8:0,16:0};
for(const dims of [[2],[3],[4],[5],[2,2],[2,3],[2,2,2],[3,3]]){
 const ops=abelian(dims),n=ops.n;
 for(let b=0;b<n;b++)for(let c=0;c<n;c++)for(let d=0;d<n;d++){
  hist[literalCycle(ops,0,b,c,d,false)]++;total++;
  if(c){hist[literalCycle(ops,0,b,c,d,true)]++;total++;}
 }
}
for(const dims of [[31],[43],[101],[3,3,3]])for(const shared of [false,true]){
 const len=literalCycle(abelian(dims),0,1,4,13,shared);
 require(len===16,"generic-offset check must reach length 16");
 hist[len]++;total++;
}
require(total===3247,"test count");
console.log(JSON.stringify({orbitSizes,cappedLabeled:325,sevenColumnTemplates:24,sevenColumnTypes:2,literalGraphs:total,hist}));
