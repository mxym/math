'use strict';

const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
const aff={};
for(let s=0;s<1<<p;s++){
 let bits=s,n=0;while(bits){bits&=bits-1;n++}if(n!==9)continue;
 const X=R.filter(i=>s&(1<<i));let c=Infinity;
 for(let a=1;a<p;a++)for(let b of R){let mask=0;for(let x of X)mask|=1<<m(a*x+b);c=Math.min(c,mask);}
 aff[c]??=R.filter(i=>c&(1<<i));
}
const levels=Object.values(aff);
const lam=X=>X.map(i=>iv[X.reduce((s,x)=>i===x?s:m(s*(i-x)),1)]);
function basis(Y){
 return Y.map(i=>{
  let f=[1],den=1;for(let y of Y)if(y!==i){
   const g=Array(f.length+1).fill(0);for(let j=0;j<f.length;j++){g[j]=m(g[j]-y*f[j]);g[j+1]=m(g[j+1]+f[j]);}
   f=g;den=m(den*(i-y));
  }return f.map(x=>m(x*iv[den]));
 });
}
let rows=[],hist={};
for(let Y of levels){
 const q=basis(Y.slice(0,5)),ly=lam(Y),T=Y.map(y=>q.map((f,i)=>m(f.reduce((s,c,j)=>s+c*y**j,0)*ly[Y.indexOf(y)]*iv[ly[i]]))),F=[];
 const rr=[];
 function rec(i,sum){
  if(i<5){for(let x=0;x<=Math.min(6,17-sum);x++){F.push(x);rec(i+1,sum+x);F.pop();}return;}
  let f=F.slice();for(let j=5;j<9;j++){let t=m(f.slice(0,5).reduce((s,a,i)=>s+a*T[j][i],0));if(t>6||sum+t>17)return;f.push(t);sum+=t;}
  if(sum!==17)return;
  const C=R.slice(0,5).map(j=>m(F.reduce((s,f,i)=>s+f*q[i][j]*iv[ly[i]],0)));
  rr.push({C,f});
 }
 rec(0,0);rows.push(rr);hist[rr.length]=(hist[rr.length]||0)+1;
}


const indexed=rows.map(rr=>Array.from({length:6},(_,nk)=>{
 const h=new Map();
 for(let row of rr){
  let key=0;for(let d=4;d>=5-nk;d--)key=17*key+row.C[d];
  const a=h.get(key)??[];a.push(row);h.set(key,a);
 }
 return h;
}));
let leaves=0,full=0,wit=[],byDepth=Array(10).fill(0); 
for(let ix=0;ix<levels.length;ix++){
 const X=levels[ix],lx=lam(X),interp=Array.from({length:9},(_,i)=>R.slice(0,5).map(d=>{
  if(i<=d)return [];
  const Y=X.slice(0,d+1);
  return Y.map((x,j)=>{
   let n=1;for(let y of Y)if(y!==x)n=m(n*(X[i]-y)*iv[m(x-y)]);
   return m(n*lx[i]*iv[lx[j]]);
  });
 }));
 for(let iy=0;iy<levels.length;iy++){
  // Swapping the two axes gives the same family; one representative suffices.
  if(iy<ix)continue;
  const seq=[],tot=Array(9).fill(0),tab=indexed[iy];
  function search(i){
   byDepth[i]++;
   if(i===9){leaves++;if(tot.every(v=>v===17)){full++;wit.push({ix,iy,X,Y:levels[iy],seq:seq.map(r=>r.f)});}return;}
   let key=0;
   for(let j=4;j>=Math.max(0,5-i);j--){
    let a=0;for(let k=0;k<=4-j;k++)a+=seq[k].C[j]*interp[i][4-j][k];
    key=17*key+m(a);
   }
   const pool=tab[Math.min(i,5)].get(key)??[];
   for(let r of pool){
    if(r.f.some((v,j)=>v+tot[j]>17))continue;
    seq.push(r);for(let j=0;j<9;j++)tot[j]+=r.f[j];
    search(i+1);
    for(let j=0;j<9;j++)tot[j]-=r.f[j];seq.pop();
   }
  }
  search(0);
 }
}
if(levels.length!==95||leaves!==2||full!==2||byDepth.join()!=="4560,672251,5902324,3073973,93012,437,8,2,2,2")throw Error("grid replay");
console.log({classes:levels.length,leaves,full,byDepth});

for(const R of wit){
 let directions=[];
 for(let s=0;s<=p;s++){
  let f=Array(p).fill(0);
  for(let i=0;i<9;i++)for(let j=0;j<9;j++)f[s===p?R.Y[j]:m(R.X[i]+s*R.Y[j])]+=R.seq[i][j];
  directions.push({s,list:f,max:Math.max(...f),uniform:f.every(x=>x===9)});
 }
 const peak=Math.max(...directions.map(v=>v.max));if(peak!==33||directions.some(d=>d.uniform))throw Error("grid geometry");
 console.log({X:R.X,Y:R.Y,peak,peakSlopes:directions.filter(d=>d.max===peak).map(d=>d.s),matrix:R.seq});
}
