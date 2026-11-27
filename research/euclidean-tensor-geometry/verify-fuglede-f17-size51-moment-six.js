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



for(const [d,k,n,m,v] of [[7,3,9,238,9036],[10,3,11,1090,1599246],[9,3,10,855,322816]]){const t=check(d,k,n);if(t.completions||t.masks!==m||t.nodes!==v)throw Error("planar census");delete t.sets;console.log(t);}
{
 const R=Array.from({length:17},(_,i)=>i),hist={};
 for(let d=2;d<=5;d++){
  let cnt={};hist[d]=cnt;let C=Array(d+1).fill(0);
  function go(k){if(k<d-1){for(let a of R){C[k]=a;go(k+1);}return;}
   let v=R.map(t=>C.reduceRight((s,a)=>(s*t+a)%17,0)),n=v.reduce((s,a)=>s+a,0),L=(51-n)/17;
   if(!Number.isInteger(L)||L<0||L>v.filter(x=>x===0).length)return;
   const peak=L>0?17:Math.max(...v);
   const w=(v.reduce((s,x)=>s+x*(x-1)/2,0)+136*L-51)/17;
   if(d===4&&(C[0]!==11||C.slice(1,4).some(Boolean)||![6,7,10,11].includes(C[4])))throw Error("quartic shape");
   if(d===5&&peak<=9&&C[0]!==1)throw Error("centered quintic constant");
   const key=[w,L,peak].join(":");cnt[key]=(cnt[key]||0)+1;
  }
  for(let a=1;a<17;a++){C[d]=a;go(0);}
 }
 if(Object.keys(hist[2]).length||Object.keys(hist[3]).length||hist[4]['4:0:11']!==4||Object.keys(hist[4]).length!==1||hist[5]['4:0:8']!==16||hist[5]['5:0:13']!==16||Object.keys(hist[5]).length!==2)throw Error("mass51 catalog");
 let mn=Infinity;for(let N=0;N<=307;N++)mn=Math.min(mn,N*N-145*N+5526);
 if(mn!==270||6*(11-3)*(11-6)>=mn)throw Error("incidence");
 console.log({hist,mn});
}
{const p=17, P=Array.from({length:289},(_,i)=>[i%17,i/17|0]),m=x=>(x%p+p)%p,R=Array.from({length:p},(_,i)=>i),inv=R.map(a=>R.find(b=>a*b%p===1));
const tr=[0,1,17];function diff(i,j){const [x,y]=P[i],[u,v]=P[j];let a=m(x-u),b=m(y-v),s=a?m(b*inv[a]):17,vv=a||b;return [s,Math.min(vv,17-vv)];}
for(let target of [9]){let visits=0,sets=[];let allow=Array(18).fill(0);for(let i=0;i<3;i++)for(let j=0;j<i;j++){let [s,v]=diff(tr[i],tr[j]);allow[s]=v;}
function go(C,tail){visits++;if(C.length===target){sets.push(C);return;}for(let i=0;i<tail.length;i++){let a=tail[i],add=[],ok=true;for(let b of C){const [s,v]=diff(a,b);if(allow[s]&&allow[s]!==v){ok=false;break;}if(!allow[s]){allow[s]=v;add.push(s);}}
 if(ok){let ts=tail.slice(i+1).filter(q=>C.every(b=>{let [s,v]=diff(q,b);return !allow[s]||allow[s]===v;})&&(()=>{let [s,v]=diff(q,a);return !allow[s]||allow[s]===v;})());if(C.length+1+ts.length>=target)go([...C,a],ts);}
 for(let s of add)allow[s]=0;
}}
go(tr,P.map((_,i)=>i).filter(i=>!tr.includes(i)));if(visits!==4090||sets.length)throw Error("equal chords");console.log({target,visits});}
}
