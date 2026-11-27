'use strict';

const P = 13;
const N = P*P;
const mod = x => (x%P+P)%P;
const inv = Array(P).fill(0);
for (let a=1; a<P; ++a)
  for (let b=1; b<P; ++b)
    if (a*b%P===1) inv[a]=b;
const dir = (a,b) => {
  const dx = mod(a%P-b%P);  
  return dx===0 ? P
    : mod((Math.floor(a/P)-Math.floor(b/P))*inv[dx]);
};
const dirs = Array.from({length:N},(_,a)=>
  Uint8Array.from({length:N},(_,b)=>dir(a,b)));
const intercept = (a,s) => s===P ? a%P
    : mod(Math.floor(a/P)-s*(a%P));
const T = [0,1,P];
const forced = (1<<0)|(1<<(P-1))|(1<<P);

function check(maxDirs, lineCap, targetSize) {
  let masks=0, nodes=0, completions=0, max=3;const sets=[];
  function searchMask(mask) {
    ++masks;
    const candidates=[];
    for (let a=2;a<N;++a)
      if (a!==P && T.every(t=>mask&(1<<dirs[a][t])))
        candidates.push(a);
    const chosen=T.slice();
    const counts=new Uint8Array((P+1)*P);
    const update=(a,delta)=>{
      for(let s=0;s<=P;++s) counts[s*P+intercept(a,s)]+=delta;
    };
    for(const t of T) update(t,1);
    function dfs(cs) {
      ++nodes;
      max=Math.max(max,chosen.length);
      if(chosen.length===targetSize){++completions;sets.push(chosen.slice());return;}
      for(let i=0;i<cs.length;++i) {
        const a=cs[i];
        if(chosen.some(b=>{
          const s=dirs[a][b];
          return counts[s*P+intercept(a,s)]>=lineCap;
        })) continue;
        const tail=[];
        for(let j=i+1;j<cs.length;++j)
          if(mask&(1<<dirs[a][cs[j]])) tail.push(cs[j]);
        chosen.push(a);
        update(a,1);
        dfs(tail);
        update(a,-1);
        chosen.pop();
      }
    }
    dfs(candidates);
  }
  function enumerate(mask,next,left) {
    if(left===0){searchMask(mask);return;}
    for(let s=next;s<P-1;++s) enumerate(mask|(1<<s),s+1,left-1);
  }
  enumerate(forced,1,maxDirs-3);
  return {maxDirs,lineCap,targetSize,masks,nodes,max,completions,sets};
}


function canonical(S){
 let best=Infinity;
 const V=Array.from({length:14},(_,i)=>i===13?[0,1]:[1,i]);
 const det=([a,b],[c,d])=>mod(a*d-b*c);
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const z=inv[det(V[c],V[b])]*det(V[c],V[a]);
  const key=S.reduce((sum,k)=>{const den=det(V[k],V[a]);return sum+(1<<(den?mod(z*det(V[k],V[b])*inv[den]):13));},0);
  best=Math.min(best,key);
 }
 return best;
}
const assert=(ok,s)=>{if(!ok)throw Error(s);};
const range=Array.from({length:14},(_,i)=>i);
const uniformMasks=[[2,6,9],[3,5,6],[3,7,11],[5,8,12],[8,9,11]].map(S=>range.filter(j=>![0,1,13,...S].includes(j)));
const allowed=new Set();
for(const S of uniformMasks){
 assert(canonical(S)===8815,"K8 mask orbit");
 for(let m=0;m<256;m++){
  const X=S.filter((v,i)=>m&(1<<i));
  if(X.length>=6)allowed.add(canonical(X));
 }
}
assert([8239,8247,8299,8303,8815].every(v=>allowed.has(v))&&allowed.size===5,"K8 direction subsets");
const counts={};
for(const n of [6,7,8]){
 let Q=check(8,2,n),D={};
 for(const S of Q.sets){
  let C={};
  for(let i=0;i<n;i++)for(let j=0;j<i;j++){
   const d=dirs[S[i]][S[j]];C[d]=(C[d]||0)+1;
  }
  const slopes=Object.keys(C).map(Number),k=canonical(slopes);
  assert(slopes.length>=6&&!allowed.has(k),"a 6/7 cap sits in a K8 pencil");
  if(slopes.length===6)assert(Object.values(C).sort().join()==="2,2,2,3,3,3","a direction has a unique secant");
  D[k]=(D[k]||0)+1;
 }
 counts[n]=D;
}
assert(JSON.stringify(counts)===JSON.stringify({6:{8311:420,8319:210,8463:280,8511:120,8635:50},7:{8311:105},8:{}}),"planar cap census");
console.log({counts,allowed:[...allowed].sort((a,b)=>a-b)});
