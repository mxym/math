// Node BigInt exact outward C mass and complete negative-receiver thresholds.
"use strict";

const N=1000n,R=200n,Q=2n*N*R,Q2=Q**2n,Q5=Q**5n,TICKS=10n**16n;
const MAX=(x,y)=>x>=y?x:y;
const ce=(x,d)=>(x+d-1n)/d;
const F=x=>{const z=Q-2n*x;return z<=0n?0n:2n*z**3n*Q2-z**5n;};
let r3=0n,r4=0n,r5=0n,r6=0n,nb=0;
for(let i=0n;i<40n;i++)for(let j=MAX(5n,i);j<170n;j++){
 const xHi=N-i-j,xLo=xHi-2n;
 r3+=ce(16n*MAX(0n,5n*((i+1n)**2n+(j+1n)**2n+xHi*xHi)-3n*N*N)*TICKS,N**4n);
 r5+=ce(128n*xHi*xHi*TICKS,5n*N**4n);
 r6+=ce((16n*xHi*xHi+20n*N*N)*TICKS,15n*N**4n);
 const um=2n*i+1n,vm=2n*j+1n,t=um*R,v=vm*R,X=2n*N-um-vm;
 const D=x=>F(x)-F(x+t)-F(x+v)+F(x+t+v);
 const at0=D(0n);
 for(let k=40n;k<100n;k++){
  const h=at0-D(k*X)-D((R-k)*X); 
  // -h/(tv) where t,v are Q based; Lipschitz of h/(tv) error = 1536/N.
  const nu=MAX(0n,-h*Q2*N+1536n*Q5*t*v);
  const de=Q5*t*v*N;
  // weight dr=1/R, dt dv=1/N², denominator normalized X_lo*k*(R-k)/R².
  r4+=ce(nu*R*TICKS,de*xLo*k*(R-k)*N);
 }
 nb++;
}

function check(x,m){if(!x)throw Error(m);}
const rTotal=r3+r4+r5+r6;
check(nb===6005,"outer t,v grid");
check(r3===965590064000000n && r4===2442051967103108n &&
      r5===1213696453120000n && r6===130637352214668n,
      "rank upper integer ticks");
check(rTotal*1000000n<475198n*TICKS,"entire C ordinary upper");
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a;}
function q(a,b=1n){a=BigInt(a);b=BigInt(b);if(b<0n){a=-a;b=-b;}const g=gcd(a,b);return [a/g,b/g];}
const a=([n,d],[m,k])=>q(n*k+m*d,d*k), s=([n,d],[m,k])=>q(n*k-m*d,d*k);
const f=([n,d],[m,k])=>q(n*m,d*k), d=([n,d],[m,k])=>q(n*k,d*m);
const pow=([n,d],k)=>q(n**BigInt(k),d**BigInt(k));
const lt=([n,d],[m,k])=>n*k<m*d;
const eq=(a,b)=>!lt(a,b)&&!lt(b,a);
const show=([n,d])=>Number(n*10n**16n/d)/1e16;
const part=(l,u,j)=>d(s(pow(u,j+1),pow(l,j+1)),q(j+1));
const beta=q(1,5000),end=q(1,25),vlo=q(3,10),vhi=q(12,25);
const tt=j=>part(beta,end,j),vv=j=>part(vlo,vhi,j);
const pp2=a(f(q(2),tt(0)),f(q(13),tt(1)));
const pp3c0=f(q(-32),f(tt(0),vv(0)));
const pp3c1=f(q(160),a(f(tt(1),vv(0)),f(tt(0),vv(1))));
const pp3c2=f(q(160),a(a(f(tt(2),vv(0)),f(tt(0),vv(2))),f(tt(1),vv(1))));
const pp3=s(a(pp3c0,pp3c1),pp3c2);
check(eq(pp2,q(8999974,100000000)),"rank-two positive exact lower");
check(eq(pp3,q(537872967168n,10000000000000n)),"rank-three exact rectangle");
const wDiff=q(867611,1000000);
const kCalc=s(a(a(wDiff,pp2),pp3),q(475198,1000000));
const k=q(5362,10000),y=q(3537083851n,10000000000n),c=q(125999484645652n,10n**15n);
const credit=f(f(q(2),c),k),old=q(378,10000),g=f(q(2,3),pow(q(475,1000),4));
check(lt(k,kCalc)&&lt(q(13512,100000),credit),"complete negative-actual block");
check(eq(a(a(old,q(4456,100000)),q(13512,100000)),q(21748,100000)),"disjoint paid total");
const wAbs=q(6388,1000000),P=a(a(q(1),wAbs),g);
const lowerGap=s(a(f(y,s(a(P,y),d(c,q(2)))),f(s(y,c),k)),d(old,q(2)));
const actualGap=s(f(y,a(P,d(y,q(2)))),d(old,q(2)));
check(lt(c,y) && lt(q(57399,100000),lowerGap) && lt(q(41162,100000),actualGap),"dyadic obstruction thresholds");
console.log(JSON.stringify({meshBoxes:nb,CupperIntegerTicks:[r3,r4,r5,r6,rTotal].map(String),
 Cupper:show(q(rTotal,TICKS)),deepRank2PositiveLower:show(pp2),deepRank3PositiveRectangle:show(pp3),
 fullNegativeMassLower:show(kCalc),wholeNegativeBlockLower:show(credit),conservativePaidBeforeSignedRest:.21748,
 dyadicGateGap:show(lowerGap),actualCenteredThreshold:show(actualGap)}));
