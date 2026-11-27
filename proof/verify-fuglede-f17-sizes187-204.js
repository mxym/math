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


const out=[];
for(const [d,k,n,masks,nodes] of [[8,5,12,3003,1176726],[8,6,11,3003,1226352],[9,3,11,5005,3801003]]){
 const r=check(d,k,n);if(r.masks!==masks||r.nodes!==nodes||r.completions||r.max!==9)throw Error("planar census");
 delete r.sets;out.push(r);
}
const weights={};
for(const m of [11,12]){
 const h={};weights[m]=h;
 for(let a=1;a<P;a++)for(let c=0;c<P;c++){
  const v=Array.from({length:P},(_,x)=>mod(a*x*x+c)), z=(P*m-v.reduce((a,b)=>a+b))/P;
  if(z<0||z>v.filter(x=>!x).length||z%1)continue;
  const w=(v.reduce((a,b)=>a+b*(b-1)/2,0)+136*z-P*m*(m-1)/2)/P;
  const k=[w,z,c].join();h[k]=(h[k]||0)+1;
 }
}
const w=weights[11];if(Object.keys(weights[12]).length||Object.keys(w).length!==4||["9,2,13","12,2,15","8,2,3","11,2,5"].some(k=>w[k]!==8))throw Error("quadratic catalog");
const p=17,d=13,r=10,q=p*p+p+1;
const low=d*r*q-Math.floor((p-(p+1)*(r+d))**2/4);
if(low!==508||d*(p-r)*(p-d)!==364)throw Error("incidence quadratic");
console.log({out,weights,low});
