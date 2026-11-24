// Run: node check_cq_prime_angular_dual_windows.js
"use strict";
(()=>{

const H=100000,A=15600,S=100000000000000n,P=4000,pp=4000n,p5=pp**5n;
const ce=(a,b)=>(a+b-1n)/b;
let upper=Array(H+1).fill(0n),lo=upper.slice(),R=0n;
for(let k=1;k*A<H;k++){
 let hu=[0n],hl=[0n];
 for(let i=0;i<H;i++){
  let a=0n,b=0n;
  if(i>=k*A){
   if(k===1){a=BigInt(H)*S/BigInt(i+1);b=ce(BigInt(H)*S,BigInt(i));}
   else{a=lo[i-A]/BigInt(i+1);b=ce(upper[i+1-A],BigInt(i));}
  }
  hu.push(hu[i]+b);hl.push(hl[i]+a);
 }
 if(k>1)R+=ce(upper[H-A],BigInt(H));
 upper=hu;lo=hl;
}
const psy=Array.from({length:P+1},(_,i)=>{const z=pp-2n*BigInt(i);return 2n*z**3n*pp**2n-z**5n;});
const theta=61n*p5/100n;
let c2=0n,c3=0n;
function clipped(h){return h<=0n?0n:h>=theta?theta:h;}
for(let i=624;i<P/2;i++){
 c2+=pp*S*clipped(p5-psy[i])/(p5*BigInt((i+1)*(P-i)));
}
for(let i=624;i<=P/3;i++)for(let j=i+1;j<=Math.floor((P-i-3)/2);j++){
 const w=P-i-j;
 const h=p5-psy[i]-psy[j]-psy[w-2];
 c3+=pp*S*clipped(h)/(p5*BigInt((i+1)*(j+1)*w));
}
// Certified k=.499 level via log((.499/.156)-1)=log(343/156).
// Using 14 finite positive atanh terms, each floored to 10^-14.
const p=187n,q=499n;let log=0n;
for(let j=0;j<14;j++){const k=BigInt(2*j+1);log+=2n*S*p**k/(q**k*k);}
const Knum=2000n*log;
const Kden=499n*S;
const denom=499n*100000n*S;
const bound=61000n*Knum+499n*(344600n*(c2+c3)-61n*3446n*R);
// Above scale for clipped . Sum: denom/1000*S => 499*100, requires 3446*100=344600.
if(bound*100n<=131n*denom)throw Error("positive high joint primal lower > 1.31");
const report=(n,d)=>Number(n*1000000000000n/d)/1e12;
console.log(JSON.stringify({roughCompUpper:report(R,S),clipped2:report(c2,S),clipped3:report(c3,S),K:report(Knum,Kden),bound:report(bound,denom)}));

})();
(()=>{

const H=20000,S=100000000000000n,P=1000,p=1000n,p5=p**5n,Theta=p5/20n;
const ce=(a,b)=>(a+b-1n)/b,B=x=>BigInt(x);
function count(A) {
 let lastLo,lastHi;const lo=[0n,S],hi=[0n,S];
 for(let r=1;r*A<H;r++){
  const gl=[0n],gu=[0n];
  for(let i=0;i<H;i++){
   let x=0n,y=0n;
   if(i>=r*A)if(r===1){x=B(H)*S/B(i+1);y=ce(B(H)*S,B(i));}
       else{x=lastLo[i-A]/B(i+1);y=ce(lastHi[i+1-A],B(i));}
   gl.push(gl[i]+x);gu.push(gu[i]+y);
  }
  if(r>1){lo[r]=lastLo[H-A]/B(H);hi[r]=ce(lastHi[H-A],B(H));}
  lastLo=gl;lastHi=gu;
 }
 return {lo,hi};
}
const left=count(1600),right=count(2100);
const sum=a=>a.reduce((s,q)=>s+q,0n);
const mband=sum(left.hi)-sum(right.lo),r5=left.lo[5]-right.hi[5];
if(!(1920n*80n**4n*(p-4n*80n)>Theta))throw Error("rank five minimum");
const psi=Array.from({length:P+1},(_,i)=>{const z=p-2n*B(i);return 2n*z**3n*p**2n-z**5n});
const f=psi.map(x=>x<0n?-x:x);
const max=(a,b)=>a>b?a:b,min=(a,b)=>a<b?a:b;
const up=(i,j)=>max(f[i],f[j]),dn=(i,j)=>i<=P/2&&P/2<=j?0n:min(f[i],f[j]);
const clip=h=>min(Theta,max(h,0n));
let g2=0n,g3=0n,g4=0n;
for(let i=80;i<105;i++){
 g2+=p*S*clip(p5-psi[i])/(p5*B((i+1)*(P-i)));
 for(let j=i+1;j<=Math.floor((P-i-3)/2);j++){
  const w=P-i-j;
  const hl=p5-psi[i]-psi[j]-psi[w-2], hh=p5-psi[i+1]-psi[j+1]-psi[w];
  g3+=p*S*clip(max(hl,-hh))/(p5*B((i+1)*(j+1)*w));
 }
 for(let j=i+1;j<=Math.floor((P-i-6)/3);j++)for(let k=j+1;k<=Math.floor((P-i-j-4)/2);k++){
  const w=P-i-j-k;
  const hl=p5-up(i,i+1)-up(j,j+1)-up(k,k+1)-up(w-3,w)+dn(i+j,i+j+2)+dn(i+k,i+k+2)+dn(P-j-k-2,P-j-k);
  const hh=p5-dn(i,i+1)-dn(j,j+1)-dn(k,k+1)-dn(w-3,w)+up(i+j,i+j+2)+up(i+k,i+k+2)+up(P-j-k-2,P-j-k);
  if(hl>hh)throw Error("invalid ordered interval");
  g4+=p*S*clip(max(hl,-hh))/(p5*B((i+1)*(j+1)*(k+1)*w));
 }
}
const Q=10000,M=62500;
const Ar=Array(M+1).fill(0n),Au=Ar.slice(),Bl=Ar.slice(),Bu=Ar.slice();
for(let i=0;i<=3*Q;i++)Ar[i]=Au[i]=2n*S;
for(let i=2*Q;i<M;i++){
 const j=i-Q,k=B(j),n=B(j+1);
 Bl[i+1]=Bl[i]+Ar[j]/n;Bu[i+1]=Bu[i]+ce(Au[j+1],k);
 if(i>=3*Q){Ar[i+1]=Ar[i]+Bl[j]/n;Au[i+1]=Au[i]+ce(Bu[j+1],k);}
}
const la=Math.floor(499*Q/80),ub=Math.floor(499*Q/105);
const Ka=Bl[la]*B(Q*1000),Da=S*B(la*80);
const Ub=Au[ub]*B(Q*1000),Db=S*B(ub*105);
const D=Da*Db, K=Ka*Db-Ub*Da;
const qS=20000n*D*S;
const lo=K*1000n*S-3446n*D*(mband-20n*(g2+g3+g4)-r5);
const print=(a,b)=>Number(a*10n**12n/b)/1e12;
if(lo*1000n<=39n*qS)throw Error("joint below .039");
console.log(JSON.stringify({bandMass:print(mband,S),rank5Count:print(r5,S),K:print(K,D),clip2:print(g2,S),clip3:print(g3,S),clip4:print(g4,S),joint:print(lo,qS)}));

})();
