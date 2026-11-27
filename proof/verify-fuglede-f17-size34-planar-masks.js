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





const Pts=Array.from({length:P+1},(_,i)=>i===P?[0,1]:[1,i]),det=([a,b],[c,d])=>mod(a*d-b*c);
const maps=[];
for(const A of Pts)for(const B of Pts)for(const C of Pts)if(A!==B&&A!==C&&B!==C){
 const z=mod(det(C,A)*inv[det(C,B)]);
 maps.push(Pts.map(v=>det(v,A)?mod(det(v,B)*z*inv[det(v,A)]):P));
}
const mask=S=>S.reduce((a,b)=>a|(1<<b),0),target9=mask([3,5,6,8,12,13,14,15,16]);
const orbit9=new Set(maps.map(f=>mask([3,5,6,8,12,13,14,15,16].map(i=>f[i]))));
const target8=[0,1,2,3,4,5,6,7,11,13],orbit8=new Set(maps.map(f=>mask(target8.map(i=>f[i]))));
const expected=[[10,10,1090,123226,0],[9,9,855,33454,7],[8,8,511,7856,5],[7,7,238,1590,0]];
for(const [k,n,masks,nodes,answers] of expected){
 const v=check(k,2,n);
 if(v.masks!==masks||v.nodes!==nodes||v.completions!==answers)throw Error('planar cap search');
 for(const S of v.sets){
  let m=0;
  for(let i=0;i<S.length;i++)for(let j=0;j<i;j++)m|=1<<dirs[S[i]][S[j]];
  const co=((1<<18)-1)^m;
  if(!(n===9?orbit9:orbit8).has(co))throw Error('wrong complementary direction orbit');
 }
 delete v.sets;
 console.log(v);
}
