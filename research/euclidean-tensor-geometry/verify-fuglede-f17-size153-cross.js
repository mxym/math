'use strict';

const P = 17;
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


const verify=(ok,s)=>{if(!ok)throw Error(s);};
const K=[0,1,4,13,16];
for(const [d,k,n,hits,nodes] of [[5,8,9,0,1413],[6,6,9,12,18361],[7,6,10,0,0],[8,6,10,0,1226352],[4,3,6,0,69]]){
 let r=check(d,k,n);
 verify(r.completions===hits&&(!nodes||r.nodes===nodes),"growth census");
 if(d===6||d===7){
  const r2=d===6?r:check(7,6,9);
  verify(r2.completions===(d===6?12:144),"cross counts");
  for(const S of r2.sets){
   const D=new Set(),long=[];
   for(let i=0;i<S.length;i++)for(let j=0;j<i;j++)D.add(dirs[S[i]][S[j]]);
   verify(D.size===6,"seven-direction cap");
   for(let s=0;s<=P;s++)for(let j=0;j<P;j++){
    const Z=S.filter(a=>intercept(a,s)===j);
    if(Z.length<5)continue;
    const vals=Z.map(a=>s===P?Math.floor(a/P):a%P);let ok=false;
    for(let a=1;a<P;a++)for(let b=0;b<P;b++)if(K.every(t=>vals.includes(mod(a*t+b))))ok=true;
    verify(Z.length===5&&ok,"cross arm");long.push(s);
   }
   verify(long.length===2&&long[0]!==long[1],"not a cross");
  }
 }
 delete r.sets;console.log(r);
}
for(let a=1;a<P;a++)verify(new Set(K.flatMap(x=>K.map(y=>mod(x-a*y)))).size>=13,"small cross difference");
