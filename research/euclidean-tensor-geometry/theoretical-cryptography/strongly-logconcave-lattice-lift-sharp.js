'use strict';
// Fixed synthetic partition of unity and analytic Gaussian convolution checks.
const A=(x,m)=>{if(!x)throw Error(m);};
const a=8*Math.log(2);
function star(x){
 x=Math.abs(x);
 if(x<=.5)return Math.exp(-a*x*x/2);
 if(x<1)return -Math.expm1(-a*(1-x)*(1-x)/2);
 return 0;
}
let exact=0,numeric=0,maxR=0;
for(let p=1;p<=13;p++)for(let q=1;q<=13;q++)for(let x=-7;x<=7;x++)for(let y=-7;y<=7;y++){
 // Unscaled exponents p*y^2+q*(x-y)^2 after completing the square, times p+q.
 const s=p+q;
 A(s*(p*y*y+q*(x-y)*(x-y))===p*q*x*x+(s*y-q*x)**2,'exact complete-square identity');exact++;
}
for(let i=-1500;i<=1500;i++){
 const x=i/431;let sm=0;
 for(let j=-5;j<=5;j++)sm+=star(x+j);
 A(Math.abs(sm-1)<1e-14,'base periodization');numeric++;
}
for(let i=1;i<=750;i++){
 const u=i*Math.log(2)/750;
 A(Math.exp(u)<=1+2*u+1e-15,'outer branch curvature');numeric++;
}
const N=4000,Y=Array.from({length:2*N+1},(_,i)=>i/N-1),vals=Y.map(star);
function calc(x,s,deriv){
 const c=1/(s*Math.sqrt(2*Math.PI)*N);let f=0,p=0,q=0;
 for(let i=1;i<Y.length-1;i++){
  const z=(x-Y[i])/s,e=Math.exp(-z*z/2)*vals[i];
  f+=e;if(deriv){p-=z*e/s;q+=(z*z-1)*e/(s*s);}
 }
 return [f*c,p*c,q*c];
}
for(let sig of [.027,.053,.11,.18,.33]){
 const alpha=a/(1+a*sig*sig);
 for(let i=-25;i<=25;i++){
  const [f,p,q]=calc(i/25,sig,true),curv=(p/f)**2-q/f;
  A(curv>=alpha-1e-6,'convolution curvature floor');numeric++;
 }
 for(let i=0;i<19;i++){
  let s=0; for(let k=-5;k<=5;k++)s+=calc(i/19+k,sig,false)[0];
  A(Math.abs(s-1)<1e-7,'smoothed periodization');numeric++;maxR=Math.max(maxR,Math.abs(s-1));
 }
}
console.log(JSON.stringify({exact,numeric,a,maxPeriodicError:maxR}));
