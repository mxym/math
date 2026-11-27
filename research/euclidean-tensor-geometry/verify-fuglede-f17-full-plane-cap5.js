'use strict';

const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1)),pw=R.map(x=>R.slice(0,13).map(i=>x**i%p)),cube=R.map(x=>x*x*x%p),four=R.map(x=>x**4%p);
const hits={},counts={};let low=18,ex;
for(let d=2;d<=12;d++){
 if(d===7||d===8)continue;
 const wanted=d>=9?[16-d,15-d,14-d]:[];
 const free=R.slice(2,d-1).filter(k=>!wanted.includes(k));
 const a=new Int16Array(d+1);a[d]=1;
 const raw=Int16Array.from(R.map(x=>pw[x][d]));
 const f=new Uint8Array(17);
 let n=0,c3=0,c4=0,cap=0;
 function dfs(k){
  if(k<free.length){const j=free[k];for(let v=0;v<p;v++){a[j]=v;dfs(k+1);for(let x=0;x<p;x++)raw[x]+=pw[x][j];}for(let x=0;x<p;x++)raw[x]-=17*pw[x][j];a[j]=0;return;}
  n++;
  for(const i of wanted){
   const k=i+d,T=2;
   let s=0;for(let j=i+1;j<d;j++)s+=a[j]*a[k-j];a[i]=m(-s*iv[T]);
  }
  let s3=0,sx=0,s4=0;
  for(let x=0;x<p;x++){
   let y=raw[x];
   if(wanted.length)y+=a[wanted[0]]*pw[x][wanted[0]]+a[wanted[1]]*pw[x][wanted[1]]+a[wanted[2]]*pw[x][wanted[2]];
   y%=p;f[x]=y;s3+=cube[y];sx+=x*cube[y];s4+=four[y];
  }
  if(s3%p||sx%p)return;c3++;
  if(s4%p)return;c4++;
  let cnt=new Uint8Array(17),dirs=0;
  for(let s=0;s<p;s++){
   cnt.fill(0);let hit=false;
   for(let x=0;x<p;x++){let t=m(f[x]-s*x);if(cnt[t])hit=true;if(++cnt[t]>5)return;}
   if(hit)dirs++;
  }
  cap++;hits[dirs]=(hits[dirs]||0)+1;
  if(dirs<low){low=dirs;ex={d,a:Array.from(a),f:Array.from(f)};}
 }
 dfs(0);counts[d]={n,c3,c4,cap};
}
if(low!==14||JSON.stringify(hits)!==JSON.stringify({14:100,15:192,16:1410,17:1421}))throw Error("full planar graph census");
console.log({counts,hits,low,ex});
