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


for(const [d,k,n,nodes] of [[8,7,10,1235865],[9,4,10,6554445]]){
 const o=check(d,k,n);if(o.nodes!==nodes||o.completions||o.max!==9)throw Error("planar census");
 delete o.sets;console.log(o);
}
const q=[];
for(let a=1;a<P;a++)for(let c=0;c<P;c++){
 const vals=Array.from({length:P},(_,x)=>mod(a*x*x+c));
 const k=(170-vals.reduce((a,b)=>a+b))/P;
 if(k<0||k%1||k>vals.filter(x=>!x).length)continue;
 const w=(vals.reduce((a,v)=>a+v*(v-1)/2,0)+136*k-17*10*9/2)/17;
 if(!q.some(([a,b])=>a===w&&b===c))q.push([w,c]);
}
const pass=[];
for(let a=0;a<q.length;a++)for(let b=a;b<q.length;b++)for(let c=b;c<q.length;c++)for(let d=c;d<q.length;d++){
 const T=[q[a],q[b],q[c],q[d]];
 if(T.reduce((s,v)=>s+v[0],0)===35&&mod(T.reduce((s,v)=>s+v[1],0))===13)pass.push(T.sort((a,b)=>a[0]-b[0]||a[1]-b[1]));
}
if(q.length!==12||Math.min(...q.map(t=>t[0]))!==8||JSON.stringify(pass)!==JSON.stringify([[[8,2],[9,8],[9,8],[9,12]]]))throw Error("tight profile census");
console.log({q,pass});
