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




for(const [d,k,n,ma,no] of [[5,2,6,21,36],[7,2,7,238,1590]]){const t=check(d,k,n);if(t.completions||t.masks!==ma||t.nodes!==no)throw Error("planar census");delete t.sets;console.log(t);}
{
const p=17,R=Array.from({length:17},(_,i)=>i),m=x=>(x%17+17)%17,iv=R.map(a=>R.find(b=>m(a*b)===1)),n=289;
const ds=Array.from({length:n},(_,a)=>Uint16Array.from({length:n},(_,b)=>{let x=m(a%17-b%17),y=m((a/17|0)-(b/17|0)),s=x?m(y*iv[x]):17,u=x||y;return s*16+Math.min(u,17-u);}));
function v(a){a=m(a);return Math.min(a,17-a);}
const masks=R.map(x=>x>8?0:((1<<x)|(1<<v(2*x))|(1<<v(9*x))));
const chosen=[0,1,17],a=Array(18).fill(511);
for(let i=0;i<3;i++)for(let j=0;j<i;j++){const z=ds[chosen[i]][chosen[j]],s=z>>4,u=z&15;a[s]&=masks[u];}
let target=17,count=0,vis=0,H=Array(20).fill(0),ex=null;
function go(C){
 ++vis;H[chosen.length]++;if(chosen.length===target){count++;ex??=chosen.slice();return;}
 if(chosen.length+C.length<target)return;
 for(let i=0;i<C.length;i++){
 const v=C[i],old=[],dsys=[],lock=Array(18).fill(0);let ok=true;
 for(let u of chosen){let z=ds[v][u],s=z>>4,r=z&15;
  if(!(a[s]&(1<<r))||++lock[s]>=3){ok=false;break;}
  old.push(a[s]);dsys.push(s);a[s]&=masks[r];}
 if(ok){let tail=[];
  for(let j=i+1;j<C.length;j++){
   let w=C[j],sel=Array(18).fill(0);let z=ds[w][v];let ok=(a[z>>4]&(1<<(z&15)))!==0;sel[z>>4]++;
   if(ok&&chosen.every(u=>{const z=ds[w][u],s=z>>4;return (a[s]&(1<<(z&15)))&&++sel[s]<3;}))tail.push(w);
  }
  if(target<=chosen.length+1+tail.length){chosen.push(v);go(tail);chosen.pop();}
 }
 for(let j=old.length-1;j>=0;j--)a[dsys[j]]=old[j];
 }
}
go(Array.from({length:n},(_,i)=>i).filter(i=>!chosen.includes(i)&&chosen.every(u=>{const z=ds[i][u];return a[z>>4]&(1<<(z&15));})));
if(count||vis!==11258)throw Error("all-doubled");console.log({name:"all-doubled",target,count,vis,H});

}
{
const p=17,R=Array.from({length:17},(_,i)=>i),m=x=>(x%17+17)%17,iv=R.map(a=>R.find(b=>m(a*b)===1)),n=289;
const ds=Array.from({length:n},(_,a)=>Uint16Array.from({length:n},(_,b)=>{let x=m(a%17-b%17),y=m((a/17|0)-(b/17|0)),s=x?m(y*iv[x]):17,u=x||y;return s*16+Math.min(u,17-u);}));
function v(a){a=m(a);return Math.min(a,17-a);}
const masks=R.map(x=>x>8?0:(1<<x));
const chosen=[0,1,17],a=Array(18).fill(511);
for(let i=0;i<3;i++)for(let j=0;j<i;j++){const z=ds[chosen[i]][chosen[j]],s=z>>4,u=z&15;if(s!==17)a[s]&=masks[u];}
let target=17,count=0,vis=0,H=Array(20).fill(0),ex=null;
function go(C){
 ++vis;H[chosen.length]++;if(chosen.length===target){count++;ex??=chosen.slice();return;}
 if(chosen.length+C.length<target)return;
 for(let i=0;i<C.length;i++){
 const v=C[i],old=[],dsys=[],lock=Array(18).fill(0);let ok=true;
 for(let u of chosen){let z=ds[v][u],s=z>>4,r=z&15;
  if(!(a[s]&(1<<r))||++lock[s]>=3){ok=false;break;}
  old.push(a[s]);dsys.push(s);if(s!==17)a[s]&=masks[r];}
 if(ok){let tail=[];
  for(let j=i+1;j<C.length;j++){
   let w=C[j],sel=Array(18).fill(0);let z=ds[w][v];let ok=(a[z>>4]&(1<<(z&15)))!==0;sel[z>>4]++;
   if(ok&&chosen.every(u=>{const z=ds[w][u],s=z>>4;return (a[s]&(1<<(z&15)))&&++sel[s]<3;}))tail.push(w);
  }
  if(target<=chosen.length+1+tail.length){chosen.push(v);go(tail);chosen.pop();}
 }
 for(let j=old.length-1;j>=0;j--)a[dsys[j]]=old[j];
 }
}
go(Array.from({length:n},(_,i)=>i).filter(i=>!chosen.includes(i)&&chosen.every(u=>{const z=ds[i][u];return a[z>>4]&(1<<(z&15));})));
if(count||vis!==3722)throw Error("one-exception");console.log({name:"one-exception",target,count,vis,H});

}
{let min=Infinity;for(let n=0;n<=307;n++)min=Math.min(min,n*n-109*n+3070);if(min!==100||5*(7-2)*(7-5)>=min)throw Error("projective incidence");console.log({min});}