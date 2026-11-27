'use strict';
// Exact geometry checks, only fixed abstract tensor arrays of small size.
const assert=(b,m)=>{if(!b)throw Error(m);};
function coords(D){let out=[[]];for(const d of D)out=out.flatMap(x=>Array.from({length:d},(_,i)=>[...x,i]));return out;}
const ss=coords([3,3,3]),cc=coords([2,2,2]),steps=[9,3,1];
let checks=0;
const B=ss.map(x=>cc.map(y=>x.reduce((z,a,i)=>z*(a===2?-1:a===y[i]?1:0),1)));
const v=[-2,1,1,0,1,0,0,0];
const w=B.map(row=>row.reduce((s,a,i)=>s+a*v[i],0));
assert(w[0]===-2&&w.some(x=>x===1),'primitive nonbinary');
for(let axis=0;axis<3;axis++)for(let i=0;i<27;i++)if(ss[i][axis]===0)assert(w[i]+w[i+steps[axis]]+w[i+2*steps[axis]]===0,'line sum');
let zeros=[[0,1,1],[1,0,1],[1,1,0],[1,1,1],[0,2,2],[2,0,2],[2,2,0]].map(x=>x[0]*9+x[1]*3+x[2]);
assert(zeros.every(i=>w[i]===0),'rank-seven vanish');
function rankMods(rows,q) {
 let a=rows.map(r=>r.map(x=>(x+q)%q)),rank=0;
 const inv=Array.from({length:q},(_,i)=>Array.from({length:q},(_,j)=>j).find(j=>i*j%q===1));
 for(let k=0;k<8;k++){
   let i=a.findIndex((r,i)=>i>=rank&&r[k]!==0);if(i<0)continue;
   [a[rank],a[i]]=[a[i],a[rank]];let m=inv[a[rank][k]];
   for(let j=rank+1;j<a.length;j++) {let f=a[j][k]*m%q;for(let l=k;l<8;l++)a[j][l]=(a[j][l]+q*q-f*a[rank][l])%q;}
   rank++;
 }return rank;
}
assert(rankMods(zeros.map(i=>B[i]),3)===7,'rank over integers');
let histB={},mat=new Int32Array(64),ids=new Int32Array(8),total=0;
function det(){
 for(let i=0;i<8;i++)for(let j=0;j<8;j++)mat[i*8+j]=B[ids[i]][j];
 let prev=1;
 for(let k=0;k<7;k++){
   let x=k;while(x<8&&mat[x*8+k]===0)x++;
   if(x===8)return 0;
   if(x!==k)for(let j=k;j<8;j++){let n=mat[k*8+j];mat[k*8+j]=mat[x*8+j];mat[x*8+j]=n;}
   let pivot=mat[k*8+k];
   for(let i=k+1;i<8;i++)for(let j=k+1;j<8;j++){
     let num=mat[i*8+j]*pivot-mat[i*8+k]*mat[k*8+j];
     assert(num%prev===0,'Bareiss integral');mat[i*8+j]=num/prev;
   }
   prev=pivot;
 }
 return Math.abs(mat[63]);
}
function dfs(k,start){
 if(k===8){let d=det();histB[d]=(histB[d]||0)+1;total++;return;}
 for(let i=start;i<=27-8+k;i++){ids[k]=i;dfs(k+1,i+1);}
}
dfs(0,0);
assert(total===2220075,'2,220,075 determinants');
let sum=0,sq=0;for(const [d,n] of Object.entries(histB)){sum+=d*n;sq+=d*d*n;}
assert(sq===3**12,'Cauchy-Binet exact');

assert(histB[0]===1691874&&histB[1]===527121&&histB[2]===1080,'exact histogram');
assert(sum===529281&&sum*19683===sq*19603,'exact volume fraction');
function projectorInt(D,x){
  let cur=[...x],stride=x.length;
  for(let ax=0;ax<D.length;ax++){
    const n=D[ax];stride/=n;
    for(let block=0;block<x.length;block+=stride*n)for(let j=0;j<stride;j++){
      let s=0;for(let u=0;u<n;u++)s+=cur[block+j+u*stride];
      for(let u=0;u<n;u++){let i=block+j+u*stride;cur[i]=n*cur[i]-s;}
    }
  }return cur;
}
function verify(D){
 let n=D.reduce((a,b)=>a*b,1),all=coords(D);
 let p=Math.min(...D.filter(x=>x%2)),a=D.indexOf(p);
 let z=all.map(id=>{
   let sign=1,sum=0;
   for(let i=0;i<id.length;i++){
     if(D[i]%2===0){if(id[i]%2===1)sign=-sign;continue;}
     if(id[i]<p){sum+=id[i];continue;}
     if((id[i]-p)%2===1)sign *= -1;
   }
   return sign*(p===Infinity||sum%p<(p+1)/2?1:-1);
 });
 let pn=projectorInt(D,z),v=pn.reduce((a,x)=>a+x*x,0);
 const e=p===Infinity?n**3:(n/p)**2*n*(p*p-1);
 assert(v===e,'exact parity projection construction');checks++;
}
for(let k=1;k<=4;k++)for(let D of coords(Array(k).fill(6)))verify(D.map(x=>x+2));
for(let D of [[2,2,2,3,5],[3,5,7,11],[4,5,8,9],[8,8,2],[2,3,19,31],[17,19,23]])verify(D);
let signVectors=0;
for(let D of [[2,2],[3,3],[2,5],[3,5],[2,2,3],[2,3,3]]){
 let n=D.reduce((a,b)=>a*b,1),p=Math.min(...D.filter(x=>x%2)),max=0;
 const e=p===Infinity?n**3:(n/p)**2*n*(p*p-1);
 for(let i=0;i<(1<<n);i++){let z=Array.from({length:n},(_,j)=>i&(1<<j)?1:-1);let x=projectorInt(D,z);max=Math.max(max,x.reduce((a,j)=>a+j*j,0));signVectors++;}
 assert(max===e,'brute-force exact parity maximum');
}
console.log(JSON.stringify({w,histB,total,sum,sq,shortfall:sq-sum,volumeFraction:[19603,19683],checkedFormats:checks,signVectors}));

