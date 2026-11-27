"use strict";

// Exact checks of arithmetic interfaces in the growing-width argument.
// Run: node verify_factor_erdos393_growing_width.js
let assertions=0, centroidFixtures=0, groupedClasses=0, ratioFixtures=0;
const check=(b,label)=>{++assertions;if(!b)throw Error(label);};
const div=(a,b)=>Math.floor(a/b);
let state=0x410f67ab;
function rand(n) {
  state=(Math.imul(state,1664525)+1013904223)>>>0;
  return (state>>>12)%n;
}
for(let r=2;r<=14;++r) for(let it=0;it<500;++it) {
  const offsets=[0];
  for(let i=1;i<r;++i)offsets.push(offsets[i-1]+1+rand(9));
  const j=BigInt(offsets[r-1]), rr=BigInt(r);
  const start=4n*j+BigInt(rand(700)+1);
  const values=offsets.map(x=>start+BigInt(x));
  const y=values.reduce((u,x)=>u+x,0n);
  const prod=values.reduce((u,x)=>u*x,1n);
  // Taylor/AM-GM consequence with all denominators cleared:
  // 0 <= m^r-prod <= 2*r*J^2*m^(r-2), m=y/r.
  const gap=y**rr-rr**rr*prod;
  check(gap>=0n&&gap<=2n*rr**3n*j*j*y**(rr-2n),"exact centroid estimate");
  ++centroidFixtures;
}
// Direct 2-adic capacity checks for small ordinary integer intervals.
function v2(n) {let v=0;while(n%2===0){++v;n/=2;}return v;}
let capacityFixtures=0;
for(let a=1;a<=640;++a)for(let j=1;j<=100;++j) {
  const b=a+j;
  let have=0,counted=0,lg=0;
  for(let t=a;t<=b;++t)have+=v2(t);
  for(let d=2;d<=b;d*=2){counted+=div(b,d)-div(a-1,d);++lg;}
  check(have===counted&&have<=j+lg,"2-adic capacity");
  ++capacityFixtures;
}
for(let n=1;n<=5000;++n) {
  let total=0,digits=0,x=n;
  for(let d=2;d<=n;d*=2)total+=div(n,d);
  while(x){digits+=x%2;x=div(x,2);}
  check(total===n-digits,"Legendre binary sum");
}

const fact=[1n];
for(let n=1;n<=80;++n)fact.push(fact[n-1]*BigInt(n));
for(let n=5;n<=80;++n) for(let r=2;r<=9;++r)
for(let beta=r;beta<n;beta+=r) {
  const nn=BigInt(n), b=BigInt(beta);
  let num=1n, den=1n;
  for(let j=1;j<beta;++j) {num*=nn;den*=nn-BigInt(j);}
  check(num*fact[n]===den*(nn**b)*fact[n-beta],"factorial-to-Pade ratio");
  ++ratioFixtures;
}
// Explicit ratios from distinct two-factor representations of 3!,5!,7!.
const pairs=[[3n,2n,3n],[5n,10n,12n],[7n,70n,72n]];
for(const [n,a,b] of pairs) {
  const y=a+b;
  check(a*b===fact[Number(n)]&&y*y-4n*fact[Number(n)]===(b-a)**2n,
    "variable shape, common degree");
}
// Check residue-class grouping independent of whether any index is witnessed.
for(let it=0;it<400;++it) {
  const n=30+rand(300), r=2+rand(15), m=r+rand(70);
  const lists=Array.from({length:r},()=>[]);
  for(let v=n;v<2*n;++v)if(rand(5)<3)lists[v%r].push(v);
  for(const a of lists) {
    let span=[0,0], wide=0;
    for(let i=2;i<a.length;++i) {
      const b1=a[i]-a[i-1], b2=a[i]-a[i-2];
      span[i%2]+=b2;
      check(r<=b1&&b1<b2&&b1%r===0&&b2%r===0,"admissible gap pattern");
      if(b2>m)++wide;
    }
    check(span.every(s=>s<n)&&(m+1)*wide<2*n,"two-step wide gap bound");
    ++groupedClasses;
  }
}
// Parameter inequalities, entirely rational. rho, theta, sigma and zeta are
// integer multiples of 1/10000. b and B have denominator 2*scale.
const sc=10000n, d=2n*sc;
function params(rho,theta,sigma,zeta,expNum) {
  const b=15n*(theta+4n*rho);
  const B=3n*sc-5n*theta-b;
  check(theta>2n*rho&&120n*rho+35n*theta<sc,"unconditional spread region");
  check((sc-2n*sigma)*B>sc*(d+b),"stronger spread margin");
  check(zeta*B>sc*d&&zeta*(d+b)<(sc-2n*sigma)*d,"both Pade exponents negative");
  check(sc-theta+2n*rho===expNum,"exceptional exponent");
}
params(10n,200n,200n,8000n,9820n);
params(50n,110n,10n,8075n,9990n);
console.log("PASS: "+assertions+" exact assertions, "+centroidFixtures+
  " centroid fixtures, "+ratioFixtures+" factorial ratios, "+groupedClasses+
  " grouped residue classes, "+capacityFixtures+" 2-adic capacity intervals");
