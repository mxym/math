'use strict';
const p=13,mod=x=>(x%p+p)%p;
const stats={};let total=0;
for(let d=2;d<=8;d++){
 const a=Array(d+1).fill(0);a[d]=1;
 const pw=Array.from({length:p},(_,x)=>Array.from({length:Math.max(5,d+1)},(_,j)=>mod(x**j)));
 let seen=0,n=0;
 function rec(i){
  if(i<d-1){for(let z=0;z<p;z++){a[i]=z;rec(i+1);}return;}
  seen++;
  for(const k of [10,11,12]){
   let q=0;for(let i=2;i<=d;i++)if(k-i>=2&&k-i<=d)q+=a[i]*a[k-i];
   if(mod(q))return;
  }
  const f=pw.map(row=>mod(a.reduce((s,v,j)=>s+v*row[j],0)));
  const mom=(b,v)=>mod(f.reduce((s,y,x)=>s+pw[x][b]*mod(y**v),0));
  if(mom(0,3)||mom(1,3)||mom(0,4))return;
  for(let s=0;s<p;s++){
   const cnt=new Uint8Array(p);
   for(let x=0;x<p;x++)if(++cnt[mod(f[x]-s*x)]>5)return;
  }
  if(d!==2)throw Error('nonparabolic candidate '+JSON.stringify(a));
  n++;
 }
 rec(2);stats[d]={seen,n};total+=seen;
}
if(total!==402235||stats[2].n!==1)throw Error('wrong check count');
console.log({stats,total});
