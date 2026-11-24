// Run: node check_cq_signed_rough_tail_envelope.js
"use strict";

function enclosure(Q,s){
 const n=Q*s,S=1000000000000n,zero=0n,ce=(a,b)=>(a+b-1n)/b;
 const al=new BigInt64Array(n+1),ah=new BigInt64Array(n+1),bl=new BigInt64Array(n+1),bh=new BigInt64Array(n+1);
 for(let i=0;i<=3*Q;i++){al[i]=ah[i]=2n*S;}
 for(let i=2*Q;i<n;i++){
  const j=i-Q;
  bl[i+1]=bl[i]+al[j]/BigInt(j+1);
  bh[i+1]=bh[i]+ce(ah[j+1],BigInt(j));
  if(i>=3*Q){
   al[i+1]=al[i]+bl[j]/BigInt(j+1);
   ah[i+1]=ah[i]+ce(bh[j+1],BigInt(j));
  }
 }
 return {diffN:String((ah[n]-bl[n])*100n),den:String(BigInt(s)*S),lower:Number(bl[n])*100/(s*Number(S)),upper:Number(ah[n])*100/(s*Number(S))};
}
function gcd(a,b){a=a<0n?-a:a;while(b)[a,b]=[b,a%b];return a;}
function Q(n,d=1){n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d;}const g=gcd(n,d);return [n/g,d/g];}
const dec=s=>{const i=s.indexOf(".");return i<0?Q(s):Q(s.slice(0,i)+s.slice(i+1),10n**BigInt(s.length-i-1));};
const a=([n,d],[m,e])=>Q(n*e+m*d,d*e),m=([n,d],[y,e])=>Q(n*y,d*e),s=(x,[n,d])=>a(x,[-n,d]),q=([n,d],[y,e])=>Q(n*e,d*y);
const p=([n,d],k)=>Q(n**BigInt(k),d**BigInt(k)),lt=([n,d],[y,e])=>n*e<y*d,show=([n,d])=>Number(n)/Number(d);
const one=Q(1),two=Q(2);
function logBounds(x){
 const z=q(s(x,one),a(x,one)),z2=p(z,2);let y=z,L=Q(0);
 for(let j=0;j<14;j++){L=a(L,q(y,Q(2*j+1)));y=m(y,z2);}
 return [m(two,L),m(two,a(L,q(y,m(Q(29),s(one,z2)))) )];
}
const l2=logBounds(Q(2)),l3=logBounds(Q(25,16));
const ll=a(m(Q(7),l2[0]),l3[0]),lh=a(m(Q(7),l2[1]),l3[1]);
if(!lt(dec("5.29"),ll)||!lt(lh,dec("5.30")))throw Error("log(200) bounds");
const cb=dec("1.062"), d=dec("17.01"), b=dec(".04"), beta=Q(1,5000);
const PhiL=a(q(cb,b),m(d,ll)),PhiH=a(q(cb,b),m(m(dec("1.001"),d),lh));
if(!lt(PhiH,Q(117))||!lt(Q(0),s(cb,m(d,b))))throw Error("envelope area");
const k=enclosure(250000,10);
const width=q(Q(k.diffN,k.den),Q(100)), lower=Q(5614584359419n,10000000000000n);
if(!lt(width,dec(".000002085"))||!lt(Q(65),m(lower,PhiL)))throw Error("genuine rough mass");
const qb=a(a(m(Q(-32),beta),m(Q(288),p(beta,2))),a(m(Q(-2720,3),p(beta,3)),m(Q(3040,3),p(beta,4))));
if(!lt(a(qb,Q(1,10n**12n)),dec("-.006388")))throw Error("tiny signed ordinary");
const e=m(Q(2),m(m(dec(".000002085"),Q(117)),Q(701)));
const gap=s(m(m(two,Q(65)),dec(".006388")),e);
if(!lt(dec(".488"),gap))throw Error("joint signed gap");
console.log(JSON.stringify({rough:k,PhiLo:show(PhiL),PhiHi:show(PhiH),massEnvelopeLower:show(m(lower,PhiL)),errorUpper:show(e),negativeGap:show(gap)}));
