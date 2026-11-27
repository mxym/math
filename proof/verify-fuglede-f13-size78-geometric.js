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

function sixCross(A){
 const ps=new Set(A),H=[0,1,3,9];
 // The hidden cross center may be absent; try every possible center.
 for(let c=0;c<N;c++)for(const a of A)for(const b of A){
  const u=[mod(a%P-c%P),mod(Math.floor(a/P)-Math.floor(c/P))];
  const v=[mod(b%P-c%P),mod(Math.floor(b/P)-Math.floor(c/P))];
  if(mod(u[0]*v[1]-u[1]*v[0])===0)continue;
  const on=(t,z)=>mod(c%P+t*z[0])+P*mod(Math.floor(c/P)+t*z[1]);
  const cross=new Set(H.flatMap(t=>[on(t,u),on(t,v)]));
  if(A.every(q=>cross.has(q)))return true;
 }
 return false;
}
const cases=[[4,6,6,0],[5,6,8,0],[5,6,6,36],[6,5,10,0],[8,5,11,0],[9,5,11,0],[9,3,10,0]];
for(const [d,c,n,want] of cases){
 const r=check(d,c,n);
 if(r.completions!==want)throw Error(JSON.stringify(r));
 for(const A of r.sets)if(!sixCross(A))throw Error("not a cross deletion");
 delete r.sets;console.log(r);
}
const H=[0,1,3,9];
for(const x of H)for(let r=1;r<P;r++){
 const s=new Set(H.flatMap(a=>H.filter(b=>b!==x).map(b=>mod(a-r*b))));
 if(s.size<9)throw Error("short full-arm difference");
}
