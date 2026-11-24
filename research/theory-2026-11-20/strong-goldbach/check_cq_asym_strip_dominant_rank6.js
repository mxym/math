// Run: node check_cq_asym_strip_dominant_rank6.js
// All bounds and branching are directed BigInt rational arithmetic.
"use strict";

(()=>{

const S=100000000000000n,H=20000,P=1000,R=200;
const B=(x)=>BigInt(x);
const ce=(n,d)=>(n+d-1n)/d;
function ordinary(a){
  const A=H*a/P;
  if(!Number.isInteger(A))throw Error('noninteger H power floor');
  let l=S,u=S,L,Hh; // rank-one true harmonic is 1 at t=1
  for(let j=1;j*A<H;j++){
    const ll=[0n],hh=[0n];
    for(let i=0;i<H;i++){
      let c=0n,d=0n;
      if(i>=j*A){if(j===1){c=HBig*S/B(i+1);d=ce(HBig*S,B(i));}
        else {c=L[i-A]/B(i+1); d=ce(Hh[i+1-A],B(i));}}
      ll.push(ll[i]+c); hh.push(hh[i]+d);
    }
    if(j>1){l+=L[H-A]/HBig;u+=ce(Hh[H-A],HBig);}
    L=ll;Hh=hh;
  }
  return [l,u];
}
const HBig=B(H);
const PP=B(P),Den=PP**5n;
const psi=Array.from({length:P+1},(_,i)=>{let z=PP-2n*B(i);return 2n*z**3n*PP**2n-z**5n});
function cells(a,b){
 let v=Array(R+1).fill(0n);
 const inj=(score,w)=>{if(score<=0n)return;let i=Number((score*B(R)-1n)/Den);if(i<0||i>R)throw Error('threshold');v[i]+=w;};
 for(let i=a;i<Math.min(b,P/2);i++)inj(Den-psi[i],PP*S/B((i+1)*(P-i)));
 for(let i=a;i<Math.min(b,P/3+1);i++){
   for(let j=i+1;j<=Math.floor((P-i-3)/2);j++){
     const w=P-i-j;
     inj(Den-psi[i]-psi[j]-psi[w-2],PP*S/B((i+1)*(j+1)*w));
   }
 }
 for(let i=R-1;i>=0;i--)v[i]+=v[i+1];
 return v;
}
const b=95;
const [mbL,mbU]=ordinary(b),pBH=cells(b,P+1);

const QI=10000,DX=2*QI,AL=53577,AH=53578,BL=42664,BH=42665;
function drift(max){
 const rlo=Array(DX+1).fill(S),rhi=rlo.slice();
 for(let i=DX;i<max;i++){
   const l=rlo[i]-ce(BigInt(2*(i+1-DX))*rhi[i-DX],BigInt(i*i));
   const h=rhi[i]-BigInt(2*(i-DX))*rlo[i+1-DX]/BigInt((i+1)**2);
   rlo.push(l>0n?l:0n);rhi.push(h>0n?h:0n);
   if(rlo[i+1]>rhi[i+1])throw Error('Dickman enclosure');
 }
 const gl=[0n],gh=[0n];for(let j=0;j<max;j++){gl.push(gl[j]+BigInt(2*j+1)*rlo[j+1]);gh.push(gh[j]+BigInt(2*j+1)*rhi[j]);}
 const dl=Array(max+1).fill(0n),dh=dl.slice(),bl=dl.slice(),bh=dl.slice();
 for(let j=2;j<=AL;j++){
  const num=BigInt(j)*BigInt(j)*2n*BigInt(DX)**2n*S*S; const den=BigInt(QI)**2n;
  dl[j]=num/(den*gh[j]);dh[j]=ce(num,den*gl[j]);
 }
 dl[AH]=dl[AL];dh[AH]=ce(BigInt(AH)**2n*2n*BigInt(DX)**2n*S*S,BigInt(QI)**2n*gl[AL]);
 for(let j=BL;j<max;j++){
   const i=j-QI;
   bl[j+1]=bl[j]+(j<BH?0n:BigInt(2*j)*dl[i]/BigInt((i+1)**2));
   bh[j+1]=bh[j]+ce(BigInt(2*(j+1))*dh[i+1],BigInt(i*i));
   if(j>=AH){dl[j+1]=dl[j]+BigInt(2*j)*bl[i]/BigInt((i+1)**2); dh[j+1]=dh[j]+ce(BigInt(2*(j+1))*bh[i+1],BigInt(i*i));}
   if(dl[j+1]>dh[j+1]||bl[j+1]>bh[j+1])throw Error('DHR enclosure');
 }
 return [bl,dh];
}
function linear(max){
 let d=Array(max+1).fill(0n),b=d.slice();
 for(let j=0;j<=3*QI;j++)d[j]=2n*S;
 for(let j=2*QI;j<max;j++){
  const i=j-QI;
  b[j+1]=b[j]+ce(d[i+1],BigInt(i));
  if(j>=3*QI)d[j+1]=d[j]+ce(b[i+1],BigInt(i));
 }
 return d;
}
const [bl,dh]=drift(125000), d1=linear(64000);
function real(a){
 const n=Math.floor(999*QI/a), m=Math.floor(499*QI/a);
 return [[bl[n]*BigInt(QI*1000)**2n,S*BigInt(n*a)**2n],[d1[m]*BigInt(QI*1000),S*BigInt(m*a)]];
}

function lowerLinear(max){
 const dn=Array(max+1).fill(0n),lb=dn.slice();
 for(let j=0;j<=3*QI;j++)dn[j]=2n*S;
 for(let j=2*QI;j<max;j++){const i=j-QI;lb[j+1]=lb[j]+dn[i]/BigInt(i+1); if(j>=3*QI)dn[j+1]=dn[j]+lb[i]/BigInt(i+1);}
 return lb;
}
const knum=lowerLinear(64000);
const point=(n,d)=>Number(n*10n**12n/d)/1e12;
const nB=Math.floor(999*QI/b),mB=Math.floor(499*QI/b);


const a=80,h=113,c=95;
if(c!==b)throw Error("wrong nested cutoff");
const n=Math.floor(999*QI/h), scale=BigInt(QI*1000)**2n, cd=S*BigInt(n*h)**2n;
const ambientN=(bl[n]*BigInt(c)-dh[n]*BigInt(a))*scale*BigInt(h);
const ambientD=cd*BigInt(a*c);
const [[,],[uAn,uAd]]=real(a);
const [[,],[uHn,uHd]]=real(h);
const kn=knum[mB]*BigInt(QI*1000),kd=S*BigInt(mB*b);
const common=ambientD*uAd*uHd*kd;
const ambient=ambientN*uAd*uHd*kd;
const uh=uHn*ambientD*uAd*kd;
const uDelta=(uAn*kd-kn*uAd)*ambientD*uHd;
if(uDelta<=0n)throw Error("bad signed band");
const [al,au]=ordinary(a),[hl,hu]=ordinary(h);
const pl=cells(a,c),ph=cells(h,P+1);
let total=0n;
for(let i=1;i<=R;i++)for(let j=1;j<=R;j++){
  const badLo=au-mbL-pl[i],badHi=hu-ph[j];
  const z=ambient*S-uh*badLo-uDelta*badHi;
  if(z>0n)total+=2n*z;
}
const denom=common*S*BigInt(R*R);
if(total*100000n<=663n*denom)throw Error("mixed true shell below .00663");
console.log(JSON.stringify({freshPair:point(total,denom),ambientOneDirection:point(ambientN,ambientD),Ua:point(uAn,uAd),Uh:point(uHn,uHd),Kc:point(kn,kd)}));

})();

(()=>{
const gcd=(a,b)=>{a=a<0n?-a:a; while(b){[a,b]=[b,a%b]}return a};
const Q=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);if(!d)throw Error("zero denominator");if(d<0n){n=-n;d=-d;}if(!n)return [0n,1n];const g=gcd(n,d);return [n/g,d/g]};
const add=([a,b],[c,d])=>Q(a*d+b*c,b*d);
const neg=([a,b])=>[-a,b]; const sub=(x,y)=>add(x,neg(y));
const mul=([a,b],[c,d])=>Q(a*c,b*d); const div=([a,b],[c,d])=>Q(a*d,b*c);
const lt=([a,b],[c,d])=>a*d<c*b;
const pow=([a,b],k)=>Q(a**BigInt(k),b**BigInt(k));
const max=(a,b)=>lt(a,b)?b:a, min=(a,b)=>lt(a,b)?a:b;
const amb=x=> Number(x[0]*10n**20n/x[1])/1e20;
const zero=Q(0),one=Q(1), A=Q(1,25);
const F=[1n];for(let i=1;i<=25;i++)F.push(F[i-1]*BigInt(i));
const choose=(n,h)=>F[n]/(F[n-h]*F[h]);
const a4=Q(2829,1000),a6=Q(3465,1000); 
if (!lt(Q(8),pow(a4,2))||!lt(Q(12),pow(a6,2)))throw Error("radical bounds");


const D=Q(26,100), beta=Q(1,5000);
function inte(B){
 const ratio=div(D,B); let series=zero,c=one, K=120;
 for(let n=0;n<K;n++){series=add(series,div(c,Q(n+5)));c=mul(c,ratio);}
 series=add(series,div(c,mul(Q(K+5),sub(one,ratio))));
 return mul(div(pow(D,5),B),series);
}
const m=mul(Q(4,3),inte(Q(8,10))),u=mul(Q(8,3),inte(Q(299,1000)));
if(!lt(m,Q(546,1000000))||!lt(u,Q(9105,1000000)))throw Error("dominant rank-six outward masses");
const z=Q(416176,10n**12n);
if(!lt(pow(beta,69),pow(z,40)))throw Error("tiny exponent");
const c0=Q(1203,1000),c4=Q(7316488,1000),A1=Q(23,5),nu=Q(51,40),kap=Q(9,2),v0=sub(one,mul(add(kap,one),beta));
const inner=add(div(A1,mul(Q(40),add(nu,Q(2)))),div(mul(Q(4),pow(A1,2)),mul(sub(kap,one),sub(Q(3),mul(Q(2),nu)))));
const bv=mul(div(Q(2),mul(Q(314159,100000),v0)),add(div(mul(c0,pow(beta,5)),Q(80)),mul(mul(c4,z),inner)));
const bvcap=Q(1044,10000);
if(!lt(bv,bvcap))throw Error("tiny absolute ordinary mass");
const mcap=Q(546,1000000),ucap=Q(9105,1000000);
const common=add(add(Q(8472,100000),Q(2380,1000000)),add(Q(1441,1000000),bvcap));
const signed=add(Q(63885,10000000),Q(111568,10000000));
const debit=add(mul(add(Q(4),mul(Q(2),signed)),mcap),mul(add(mcap,mul(Q(2),common)),ucap));
if(!lt(debit,Q(573,100000)))throw Error("fair incremental debit > .00573");
if(!lt(Q(89,100000),sub(Q(663,100000),Q(573,100000))))throw Error("fresh surplus < .00089");
console.log(JSON.stringify({mass:amb(m),receiver:amb(u),tinyMass:amb(bv),debit:amb(debit)}));

})();
