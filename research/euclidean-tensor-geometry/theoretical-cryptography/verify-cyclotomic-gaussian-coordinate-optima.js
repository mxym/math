"use strict";
// Exact finite geometric side case: A_2^* tensor A_4^*. No samples.
const grid=[];
for(let i=0;i<3;++i){
  grid[i]=[];
  for(let j=0;j<5;++j){
    grid[i][j]=Array.from({length:8},(_,k)=>{
      const r=k>>2,t=k&3;
      return (i===r?1:i===2?-1:0)*(j===t?1:j===4?-1:0);
    });
  }
}
const raw=[];
const add=(a,b,s)=>a.map((v,i)=>v+s*b[i]);
for(let i=0;i<3;++i)for(let j=0;j<5;++j){
  raw.push([0,grid[i][j]]);
  for(let k=j+1;k<5;++k)raw.push([1,add(grid[i][j],grid[i][k],1)]);
  for(let l=i+1;l<3;++l)for(let k=0;k<5;++k)
    if(k!==j)raw.push([2,add(grid[i][j],grid[l][k],-1)]);
}
const unique=new Map();
for(const [level,v] of raw){
  const s=Math.sign(v.find(x=>x!==0)), w=v.map(x=>s*x);
  const key=w.join(",");
  if(unique.has(key)&&unique.get(key).level!==level)throw Error("duplicate shell");
  unique.set(key,{level,v:w});
}
const data=[...unique.values()];
const ip=(a,b)=>a.reduce((out,x,i)=>out+b.reduce((s,y,j)=>s+x*y*
 ((i>>2)===(j>>2)?2:-1)*((i&3)===(j&3)?4:-1),0),0);
const G=data.map(a=>data.map(b=>ip(a.v,b.v)));
const shells=[0,1,2].map(k=>data.filter(x=>x.level===k).length);
if(shells.join(",")!=="15,30,60")throw Error("shell sizes");
for(let i=0;i<data.length;++i)
  if(G[i][i]!==[8,12,14][data[i].level])throw Error("shell norms");
const pair=(a,b)=>(15-G[a][a])*(15-G[b][b])>=G[a][b]**2;
function psd(ids,strict=false){
  const M=ids.map((i,m)=>ids.map((j,n)=>BigInt(m===n?15-G[i][i]:-G[i][j])));
  let prev=1n;
  for(let i=0;i<M.length;++i){
    const p=M[i][i];
    if(p<0n || (strict&&p===0n))return false;
    if(p===0n){for(let j=i+1;j<M.length;++j)if(M[i][j]!==0n)return false;continue;}
    for(let j=i+1;j<M.length;++j)for(let k=j;k<M.length;++k){
      const n=p*M[j][k]-M[i][j]*M[i][k];
      if(n%prev!==0n)throw Error("nonexact PSD check");
      M[k][j]=M[j][k]=n/prev;
    }
    prev=p;
  }
  return true;
}
function run(level,strict=false){
  const i=data.findIndex(x=>x.level===level);
  const cand=data.flatMap((x,j)=>j!==i&&x.level<=level&&pair(i,j)?[j]:[]);
  let tested=0,found=null;
  function dive(sel,left){
    if(found)return;
    if(sel.length===8){found=sel;return;}
    if(sel.length+left.length<8)return;
    for(let k=0;k<left.length;++k){
      if(sel.length+left.length-k<8)break;
      const j=left[k], T=[...sel,j];
      ++tested;
      if(!psd(T,strict))continue;
      dive(T,left.slice(k+1).filter(v=>pair(v,j)));
    }
  }
  dive([i],cand);
  return {shell:level,candidates:cand.length,tested,found};
}

const longCase=run(2), mediumCase=run(1);
if(longCase.found||mediumCase.found||longCase.candidates!==21||
   mediumCase.candidates!==31||longCase.tested!==50||mediumCase.tested!==888)
  throw Error("unexpected finite shell result");
console.log(JSON.stringify([longCase,mediumCase]));
function determinant(A){
  if(A.length===0)return 1n;
  const M=A.map(a=>a.map(BigInt)), n=M.length;
  let old=1n, sign=1n;
  for(let i=0;i<n-1;++i){
    let p=i;
    while(p<n&&M[p][i]===0n)++p;
    if(p===n)return 0n;
    if(p!==i){[M[p],M[i]]=[M[i],M[p]];sign=-sign;}
    const pivot=M[i][i];
    for(let j=i+1;j<n;++j)for(let k=i+1;k<n;++k){
      const num=pivot*M[j][k]-M[j][i]*M[i][k];
      if(num%old!==0n)throw Error("nonexact determinant division");
      M[j][k]=num/old;
    }
    for(let j=i+1;j<n;++j)M[j][i]=0n;
    old=pivot;
  }
  return sign*M[n-1][n-1];
}
function tree(E){
  const parent=Array.from({length:8},(_,i)=>i), root=i=>parent[i]===i?i:root(parent[i]);
  for(const e of E){
    const a=root(Math.floor(e/5)),b=root(3+e%5);
    if(a===b)return false;
    parent[a]=b;
  }
  return true; // seven edges on eight vertices and no cycle
}
let tested=0, trees=0;
const edges=grid.flat();
function comb(omit,j){
  if(omit.length===7){
    const included=edges.filter((_,i)=>!omit.includes(i)),
          A=Array.from({length:8},(_,i)=>included.map(col=>col[i]));
    const d=determinant(A), t=tree(omit);
    if(t ? d!==1n&&d!==-1n : d!==0n)throw Error("tree complement determinant");
    ++tested;if(t)++trees;
    return;
  }
  for(let i=j;i<=15-(7-omit.length);++i)comb([...omit,i],i+1);
}
comb([],0);
if(tested!==6435||trees!==2025)throw Error("tree counts");
console.log("Basis/tree equivalence checked on "+tested+" subsets: "+trees+" integral bases.");
