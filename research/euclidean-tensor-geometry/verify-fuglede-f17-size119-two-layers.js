'use strict';

const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
const aff={};
for(let s=0;s<1<<p;s++){
 let bits=s,n=0;while(bits){bits&=bits-1;n++}if(n!==7)continue;
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
 const q=basis(Y.slice(0,4)),ly=lam(Y),T=Y.map(y=>q.map((f,i)=>m(f.reduce((s,c,j)=>s+c*y**j,0)*ly[Y.indexOf(y)]*iv[ly[i]]))),F=[];
 const rr=[];
 function rec(i,sum){
  if(i<4){for(let x=0;x<=Math.min(7,17-sum);x++){F.push(x);rec(i+1,sum+x);F.pop();}return;}
  let f=F.slice();for(let j=4;j<7;j++){let t=m(f.slice(0,4).reduce((s,a,i)=>s+a*T[j][i],0));if(t>7||sum+t>17)return;f.push(t);sum+=t;}
  if(sum!==17)return;
  const C=R.slice(0,4).map(j=>m(F.reduce((s,f,i)=>s+f*q[i][j]*iv[ly[i]],0)));
  rr.push({C,f});
 }
 rec(0,0);rows.push(rr);hist[rr.length]=(hist[rr.length]||0)+1;
}


const indexed=rows.map(rr=>Array.from({length:5},(_,nk)=>{
 const h=new Map();
 for(let row of rr){
  let key=0;for(let d=3;d>=4-nk;d--)key=17*key+row.C[d];
  const a=h.get(key)??[];a.push(row);h.set(key,a);
 }
 return h;
}));
let leaves=0,full=0,wit=[],byDepth=Array(10).fill(0); 
for(let ix=0;ix<levels.length;ix++){
 const X=levels[ix],lx=lam(X),interp=Array.from({length:7},(_,i)=>R.slice(0,4).map(d=>{
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
  const seq=[],tot=Array(7).fill(0),tab=indexed[iy];
  function search(i){
   byDepth[i]++;
   if(i===7){leaves++;if(tot.every(v=>v===17)){full++;wit.push({ix,iy,X,Y:levels[iy],seq:seq.map(r=>r.f)});}return;}
   let key=0;
   for(let j=3;j>=Math.max(0,4-i);j--){
    let a=0;for(let k=0;k<=3-j;k++)a+=seq[k].C[j]*interp[i][3-j][k];
    key=17*key+m(a);
   }
   const pool=tab[Math.min(i,4)].get(key)??[];
   for(let r of pool){
    if(r.f.some((v,j)=>v+tot[j]>17))continue;
    seq.push(r);for(let j=0;j<7;j++)tot[j]+=r.f[j];
    search(i+1);
    for(let j=0;j<7;j++)tot[j]-=r.f[j];seq.pop();
   }
  }
  search(0);
 }
}
if(levels.length!==75||leaves||full||byDepth.join()!=="2850,661614,9049191,7123972,258953,282,0,0,0,0")throw Error("layer grid");
console.log({classes:levels.length,leaves,full,byDepth});

