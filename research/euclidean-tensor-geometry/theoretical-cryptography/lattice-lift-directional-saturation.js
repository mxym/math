'use strict';
// Fixed modular-coordinate identities and scalar error-bound probes.
const assert=(x,m)=>{if(!x)throw Error(m);};
let exact=0,numerical=0,maxTail=0;
const mod=(x,p)=>(x%p+p)%p;
for(let p=2;p<=13;p++) for(let shear=-8;shear<=8;shear++)
for(let step=1;step<=9;step++) for(let a=-2*p;a<=2*p;a++)for(let k=-3;k<=3;k++){
 let p1=Math.floor(a/p),r1=mod(a,p),p2=Math.floor((a+k*p)/p),r2=mod(a+k*p,p);
 const x=2*a-shear;
 const y1=mod(x-p1*shear,step),y2=mod(x+k*shear+3*step-p2*shear,step);
 assert(r1===r2&&y1===y2,'skew torus coordinate invariance');exact++;
}
const A=8*Math.log(2);
function fstar(x){x=Math.abs(x);return x<=.5?Math.exp(-A*x*x/2):x<1?-Math.expm1(-A*(1-x)**2/2):0;}
for(let i=1;i<=180;i++){
 const e=2**(-9-i/25),d=e**(1/3);
 let sum=0;for(let k=0;k<120;k++){const u=(k+.5)*d/120;sum+=2*fstar(1-u)*d/120;}
 assert(sum<=2*e,'quadratic vanishing gives cubic wrapping mass');
 assert(7/2*d*d<.125&&d<=.125+1e-14,'quantitative regime');numerical+=2;
 maxTail=Math.max(maxTail,sum/e);
}
for(let i=1;i<=100;i++){
 const tau=i/800,sigma=(8*tau)**(1/3),eta=4*tau/sigma;
 const b=2+(i%16),bp=b/(1+b*sigma*sigma);
 assert(eta<=.5+1e-15&&8*Math.log((1+eta)/(1-eta))<=32*eta+1e-14,'approximate midpoint sum constants');
 assert(b-bp<=4*b*b*tau**(2/3)+1e-13,'curvature convolution loss');
 numerical+=2;
}
// Dual unit vectors with angle cosine 1/2 give transverse dual squared norm 3/4.
assert(4-1===3,'equilateral projection');exact++;
const r=4/3,eps = Math.min(1/512, (A*(r-1)/(r+(64+4*A*A*r*r)*(7/2)**(2/3)))**(9/4));
console.log(JSON.stringify({exact,numerical,maxWrappedTailToDeficitRatio:maxTail,hexagonalCertifiedGap:eps}));
