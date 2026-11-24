// Run: node check_cq_rank6_paired_capacity.js
// Arithmetic checks on the physical tagged upper/incompatible third-label lower.
"use strict";
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

const tFloor=Q(1,5000),absA=[Q(1,5000),Q(1,25)],bw=Q(1,1000);
function logLo(y){
 const z=div(sub(y,one),add(y,one));
 if(lt(z,zero)||!lt(z,one))throw Error("log domain");
 const z2=pow(z,2);let c=z,s=zero;
 for(let j=0;j<14;j++){s=add(s,div(c,Q(2*j+1)));c=mul(c,z2);}
 return mul(Q(2),s);
}
const Y=10n**15n, tick=x=>x[0]*Y/x[1];
let n=0, rebate=0n,squared=0n,sumBy={},u=zero,over=zero,rMass=0n,rCount=0,overTick=0n;
for(let i=0;i<40;i++){
 const t0=max(Q(i,1000),tFloor),t1=Q(i+1,1000);
 const Ht=logLo(div(t1,t0));
 for(let j=Math.max(i+1,5);j<170;j++){
  const v0=Q(j,1000),v1=Q(j+1,1000);
  const X0=sub(sub(one,t1),v1),X1=sub(sub(one,t0),v0);
  const B=add(Q(499,1000),div(v0,Q(2))),E=sub(sub(B,t1),v1);
  const z=add(max(div(X1,Q(5)),v1),Q(1,10000));
  if(!lt(mul(Q(2),z),E))continue;
  if(!lt(E,mul(Q(4),z)))throw Error('f1 exact range');
  const P=[Q(-32),mul(Q(192),t1),mul(Q(168),v1),mul(Q(-320),pow(v0,2)),mul(Q(-480),mul(t0,v0)),mul(Q(-320),pow(t0,2)),mul(Q(180),pow(v1,3)),mul(Q(320),mul(t1,pow(v1,2))),mul(Q(360),mul(pow(t1,2),v1)),mul(Q(160),pow(t1,3)),div(mul(Q(-4),mul(pow(t0,2),sub(Q(2),pow(t0,2)))),v1)].reduce(add,zero);
  const U4=mul(mul(t0,v0),P);
  const K3=mul(mul(Q(16),mul(t0,v0)),mul(X0,sub(mul(Q(5),add(add(pow(t0,2),pow(v0,2)),pow(X0,2))),Q(3))));
  const K4=mul(mul(Q(4),neg(U4)),div(mul(z,sub(X0,z)),pow(X1,2)));
  const K5=mul(Q(1920),mul(mul(t0,v0),mul(pow(z,2),sub(X0,mul(Q(2),z)))));
  const K6=mul(Q(5760),mul(mul(t0,v0),mul(pow(z,3),sub(X0,mul(Q(3),z)))));
  const K=min(min(K3,K4),min(K5,K6));
  if(!lt(zero,K)) continue;
  ++n;
  const Eupper=sub(sub(Q(499,1000),t1),v1);
  if(!lt(zero,Eupper)||!lt(div(Eupper,Q(3)),z))throw Error("actual upper cutoff");
  u=add(u,div(mul(Q(200),mul(sub(t1,t0),sub(v1,v0))),Eupper));
  const area=mul(sub(t1,t0),sub(v1,v0));
  const zUp=add(div(E,Q(3)),Q(1,10000));
  if(!lt(zUp,z)||!lt(zUp,E))throw Error("overcut for C");
  const fU=div(mul(Q(200),area),E);
  overTick+=(fU[0]*Y+fU[1]-1n)/fU[1];
  const logReject=x=>{
    const z=div(sub(x,one),add(x,one)), z2=pow(z,2);
    if(lt(z,zero)||!lt(z,one))throw Error('reject log range');
    let c=z,s=zero;for(let i=0;i<6;i++){s=add(s,div(c,Q(2*i+1)));c=mul(c,z2);}
    return mul(Q(2),s);
  };
  for(let h=Math.max(j+1,120);h<170;h++){
    const r0=Q(h,1000),r1=Q(h+1,1000);
    if(!lt(zUp,r0)||lt(z,r1))continue;
    const Z3=add(r1,Q(1,10000));
    const Bb=add(Q(499,1000),div(r0,Q(2)));
    const L3=sub(sub(sub(Bb,t1),v1),r1);
    if(!lt(mul(Q(2),Z3),L3))continue;
    if(!lt(L3,mul(Q(4),Z3))||!lt(add(t1,v1),L3)||!lt(Q(106,1000),sub(Bb,r1)))throw Error("rejected rail");
    rCount++;
    const term=mul(mul(Q(100),area),mul(logReject(div(r1,r0)),div(mul(Q(2),logReject(sub(div(L3,Z3),one))),L3)));
    rMass+=tick(term);
  }
  const hv=logLo(div(v1,v0));
  const c=mul(div(mul(Q(2),logLo(sub(div(E,z),one))),E),mul(Ht,hv));
  rebate+=tick(mul(c,K));squared+=tick(mul(c,pow(K,2)));
  const k=[K3,K4,K5,K6].findIndex(x=>!lt(x,K)&&!lt(K,x))+3;
  sumBy[k]??=0n;sumBy[k]+=tick(mul(c,K));
 }
}
if(n!==5970||rebate!==92609478893615n||squared!==1281239179835n)throw Error("deep prime rebate certificate");
if(rCount!==46292 || rMass*1000000n<=22699n*Y || (overTick-rMass)*1000000n>=2742208n*Y) throw Error("true rank-six capacity discount");
const newBound=Q(2742208,1000000),m6Lower=Q(2197,100000),target=Q(1749,100000);
if(!lt(target,mul(Q(2),mul(m6Lower,sub(u,newBound)))))throw Error("safe incremental saving");
console.log(JSON.stringify({n,rCount,shortfall:Number(rMass)/1e15,upperBeforeRejected:Number(overTick)/1e15,upperAfter:Number(overTick-rMass)/1e15,oldReceiver:amb(u)}));
