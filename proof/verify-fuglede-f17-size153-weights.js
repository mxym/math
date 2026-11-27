'use strict';
const p=17,m=9,W=1260,C=36,mod=x=>(x%p+p)%p;
const check=(x,msg)=>{if(!x)throw Error(msg);};
const out=[];
for(let d=1;d<=4;d++){
 let n=0,min=Infinity;
 for(let a=1;a<p;a++)for(let v=0;v<p**Math.max(0,d-1);v++){
  const c=Array.from({length:d-1},(_,i)=>Math.floor(v/p**i)%p);
  const f=Array.from({length:p},(_,x)=>mod(a*x**d+c.reduce((s,b,i)=>s+b*x**i,0)));
  const lifts=(m*p-f.reduce((s,b)=>s+b,0))/p;
  if(lifts%1||lifts<0||lifts>f.filter(t=>!t).length)continue;
  const w=(f.reduce((s,t)=>s+t*(t-1)/2,0)+136*lifts-p*m*(m-1)/2)/p;
  check(Number.isInteger(w)&&w>0,"weight");n++;min=Math.min(min,w);
 }
 out.push({d,n,min});
}
check(out.map(o=>o.min).join()==="12,8,6,4","profile minimum");
const Q=p*p+p+1;
let u=18*W*W-C*W*Q,v=15984*Q-W*W;
check(u>0&&v>0&&BigInt(u)**2n>17n*BigInt(v)**2n,"polarity mixing");
console.log({out,u,v});
