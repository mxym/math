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


const perm=[];
for(let a of T)for(let b of T)for(let c of T)if(a!==b&&a!==c&&b!==c){
 const modv=(s,d)=>[mod(d%P-s%P),mod((d/P|0)-(s/P|0))];
 const [x,y]=modv(a,b),[u,v]=modv(a,c);
 perm.push(Array.from({length:P+1},(_,s)=>{const i=s===P?0:1,j=s===P?1:s;
 const X=mod(x*i+u*j),Y=mod(y*i+v*j);return X?mod(Y*inv[X]):P;}));
}
function masksymm(mask){
 for(const f of perm){let S=0;for(let d=0;d<=P;d++)if(mask&(1<<d))S|=1<<f[d];if(S<mask)return false;}
 return true;
}

function check(maxDirs, lineCap, targetSize) {
  let masks=0, nodes=0, completions=0, max=3;const sets=[];
  function searchMask(mask) {
    if(!masksymm(mask))return;
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
      if(chosen.length+cs.length<targetSize)return;
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




const F=Array.from({length:17},(_,i)=>i);
const templates={5:check(6,2,5).sets,6:check(6,2,6).sets};
const input=[[0,1],[0,2],[0,15],[0,16],[1,13],[1,14],[2,0],[2,14],[3,9],[3,12],[4,7],[4,8],[6,6],[6,7],[6,12],[6,13],[6,15],[6,16],[8,11],[9,6],[11,1],[11,2],[11,4],[11,5],[11,10],[11,11],[13,9],[13,10],[14,5],[14,8],[15,0],[15,3],[16,3],[16,4]];
const f0=input.map(k=>typeof k==='number'?[k%17,Math.floor(k/17)]:k).sort((a,b)=>a[0]-b[0]||a[1]-b[1]);
const n=f0.length;
function canon(q,t){
 const step=inv[mod(t[1]-t[0])],r=q.map((y,i)=>mod(y-q[0]-((q[1]-q[0])*step)%17*(t[i]-t[0])));
 const a=r.find(x=>x);if(!a)return null;return r.map(x=>mod(x*inv[a]));
}
function models(t){let ans=new Map();
 for(let H of templates[t.length])for(let a of F)for(let b of F){
  if(!a&&!b)continue;
  let T=H.map(j=>mod(a*(j%17)+b*(j/17|0))),Q=H.map(j=>b?j%17:j/17|0);
  if(new Set(T).size!==t.length)continue;
  for(let c of F){let z=T.map(x=>mod(x+c));if(z.some(v=>!t.includes(v)))continue;
   let r=canon(t.map(v=>Q[z.indexOf(v)]),t);if(r)ans.set(String(r),r);
  }
 }return [...ans.values()];
}
const lines=[];for(let slope=0;slope<=17;slope++)for(let shift of F){
 const I=f0.map(([x,y],i)=>(slope===17?x:mod(y-slope*x))===shift?i:-1).filter(i=>i>=0);
 if(I.length<5)continue;
 const t=I.map(i=>f0[i][slope===17?1:0]);
 const variants=models(t);lines.push({slope,shift,I,t,variants});
}
if(n!==34||lines.length!==16||lines.some(l=>l.variants.length))throw Error("witness lifting rejection");
console.log({N:n,templates:Object.fromEntries(Object.keys(templates).map(k=>[k,templates[k].length])),rich:lines.map(({slope,shift,t,variants})=>({slope,shift,t,opts:variants.length})),invalid:lines.filter(l=>!l.variants.length).length});

const PX=F.map(x=>{let a=[1];while(a.length<17)a.push(mod(x*a.at(-1)));return a;});
let total=0,nonuniform=[];
for(let j=0;j<=17;j++){
 const g=Array(17).fill(0);for(let [x,y] of f0)g[j===17?y:mod(x+j*y)]++;
 if(g.some(v=>v!==2)){
  const c=Array.from({length:16},(_,i)=>mod(-g.reduce((s,u,t)=>s+u*PX[t][15-i],0)));
  if(!c[9]||c[8]||c.slice(10).some(Boolean)||Math.max(...g)>6)throw Error("witness profile degree");
  nonuniform.push(j);
 }
 total+=(g.reduce((s,v)=>s+v*v,0)-68)/2;
}
if(total!==255||String(nonuniform)!=="0,1,2,3,4,5,6,7,8,9,11,15")throw Error("witness Radon validation");
console.log({total,nonuniform});
