'use strict';

const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1)),Q=R.map(()=>[]);
for(let a=1;a<p;a++)for(let b of R)for(let c of R){
 const f=R.map(x=>m(a*x**3+b*x+c)),z=f.filter(x=>!x).length,l=(85-f.reduce((s,n)=>s+n,0))/p;
 if(l<0||l%1||l>z)continue;if(l)throw Error("unexpected zero lift");Q[a].push({b,c,f});
}
let lead=0,cong=0,valid=0,H={},maxHist={},ex;
for(let s=2;s<p;s++)for(let t=s+1;t<p;t++)for(let a4=1;a4<p;a4++){
 const a3=m((t-t*t)*a4*iv[m(s*s-s)]),a2=m(-s*a3-t*a4),a0=m(-a2-a3-a4),a1=m(-a2-a3*s**3-a4*t**3);
 if(!a0||!a1||!a2||!a3)continue;lead++;
 for(let f0 of Q[a0])for(let f1 of Q[a1])for(let f2 of Q[a2]){
  const X=-f0.b-f2.b,Y=-f1.b-f2.b,b4=m((Y-s*X)*iv[m(t-s)]),b3=m(X-b4);
  for(let f3 of Q[a3])for(let f4 of Q[a4]){
   if(f3.b!==b3||f4.b!==b4||m(f0.c+f1.c+f2.c+f3.c+f4.c)!==3)continue;cong++;
   let z=R.flatMap(x=>R.map(y=>(f0.f[x]+f1.f[y]+f2.f[m(x+y)]+f3.f[m(x+s*y)]+f4.f[m(x+t*y)]-20)/17));
   if(z.some(n=>n%1||n<0||n>5))continue;valid++;
   let k=Math.max(...z);maxHist[k]=(maxHist[k]||0)+1;H[s+","+t]=(H[s+","+t]||0)+1;ex??={s,t,a:[a0,a1,a2,a3,a4],c:[f0.c,f1.c,f2.c,f3.c,f4.c]};
  }
 }
}
if(lead!==1680||cong||valid||Q.slice(1).some(x=>x.length!==4))throw Error("cubic K13 census");
console.log({lead,cong,valid});

let quad=0;
for(let a=1;a<p;a++)for(let c=0;c<p;c++){
 const f=R.map(x=>m(a*x*x+c)),k=(85-f.reduce((s,n)=>s+n,0))/p;
 if(Number.isInteger(k)&&k>=0&&k<=f.filter(x=>!x).length)quad++;
}
if(quad)throw Error("quadratic projection profile");
const f=n=>n*n-181*n+8596,w=n=>(n-4)*(n-7);
let g2=Infinity,g3=Infinity;
for(let a=13;a<=17;a++)for(let b=13;b<=17;b++){
 g2=Math.min(g2,f(64+a+b)-w(a)-w(b)-200);
 for(let c=13;c<=17;c++)g3=Math.min(g3,f(60+a+b+c)-w(a)-w(b)-w(c)-160);
}
if(g2!==2||g3!==156)throw Error("heavy-pencil incidence");
console.log({quad,g2,g3});
