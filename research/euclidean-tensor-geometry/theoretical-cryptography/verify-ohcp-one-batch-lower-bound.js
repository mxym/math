"use strict";
// Standalone inequalities and quadrature checks for an information lower bound.
let exact=0, floating=0;
function check(ok,msg,fp=false){
  if(!ok)throw Error(msg);
  if(fp)++floating;else ++exact;
}
function simpson(f,l,r,n=4096){
  let out=f(l)+f(r);
  const d=(r-l)/n;
  for(let j=1;j<n;++j)out+=(j%2?4:2)*f(l+j*d);
  return out*d/3;
}
for(let k=1;k<=80;++k){
  // Volume inflation at epsilon=1/(128 k), R=1/16.
  check(BigInt(2*k+1)**BigInt(k)<2n*BigInt(2*k)**BigInt(k),"volume ratio");
  // At most floor(k/16) coordinates may cost 16 epsilon^2 / k.
  check(BigInt(Math.floor(k/16))*16n<=BigInt(k)&&
        BigInt(Math.floor(k/16)+1)*16n>BigInt(k),"signed-cube error budget");
  for(let shift=1;shift<=64;++shift){
    const a=Array.from({length:k},(_,i)=>BigInt((i*i+37*i*shift)%101-50));
    const sum=a.reduce((x,v)=>x+v*v,0n);
    let signedSum=0n;
    for(const x of a)for(const e of [-1n,1n])signedSum+=(e*x)**2n;
    check(signedSum===2n*sum,"isotropic signed-direction averaging");
  }
  if(k>=3)check(k<=3*(k-2),"layer-cake constant");
}
for(const s of [1/256,1/16,1/2,1,4,16]){
  // Polar integration in u=r/s, avoiding a scale-specific quadrature.
  const v=simpson(u=>8*Math.PI*u**3*Math.exp(-2*u*u),0,8);
  check(Math.abs(v-Math.PI)<4e-10,"2D integrated gradient",true);
  for(const ratio of [0.0001,0.001,0.02,0.7,1,1.9,3.1,5,12]){
    const v=s*simpson(x=>(Math.exp(-x*x)-Math.exp(-((x+ratio)**2)))**2,-ratio-9,9);
    const w=2*Math.sqrt(Math.PI/2)*s*(-Math.expm1(-ratio*ratio/2));
    check(Math.abs(v-w)<8e-11*s,"1D shifted Gaussian L2",true);
    check(w<=2*Math.sqrt(Math.PI/2)*Math.min(s,(s*ratio)**2/s),"1D bound",true);
  }
}
for(const kappa of [20,23,35,45,250,880])
for(const t of [0,.03,.2,.7,1,2,4,8,12,20])
for(const r of [.25,.3,.375,.49,.5]){
  const u=Math.exp(2*t)*r*r;
  const f=2/kappa*Math.exp(-u);
  check(Math.log(kappa)+u-t/kappa>=0,"PRS tail condition",true);
  check(4/kappa*u*Math.exp(-u)<=kappa,"PRS Lipschitz condition",true);
  if(t===0)check(f>=1/kappa,"PRS advantage condition",true);
}
for(let j=2;j<=100;++j){
  const d=2**(-j), L=Math.log(1/d), exactBinary=(1-2*d)*(L+Math.log1p(-d));
  check(exactBinary>=L/4,"high-confidence data processing constant",true);
}
console.log("Hidden-center lower-bound checks: "+exact+" exact cases and "+floating+" floating illustrations passed.");
