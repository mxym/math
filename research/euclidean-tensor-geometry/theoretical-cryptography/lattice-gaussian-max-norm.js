'use strict';
// Fixed rational Euclidean lattice: certified finite interval arithmetic, no external inputs.
const assert=(b,m)=>{if(!b)throw Error(m);};
const W=1n<<70n, P=W**3n,C=2244n;
const ceilDiv=(p,q)=>(p+q-1n)/q;
const fac=[1n]; for(let i=1n;i<=24n;i++)fac.push(fac[Number(i)-1]*i);
function weight(A,B){
 A=BigInt(A);B=128n*BigInt(B);
 assert(0n<=A&&A<=B,'alternating series range');
 const den=B**24n*fac[24];let n=0n,least=0n;
 for(let i=0;i<=24;i++){n+=(-A)**BigInt(i)*B**BigInt(24-i)*(fac[24]/fac[i]);if(i===23)least=n;}
 let lo=W*least/den, hi=ceilDiv(W*n,den);
 for(let k=0;k<7;k++){lo=lo*lo/W;hi=ceilDiv(hi*hi,W);}
 assert(0n<=lo&&lo<=hi&&hi<=W,'positive outward enclosure');
 return [lo,hi];
}
const rows=(m,map)=>Array.from({length:2*m+1},(_,i)=>{let j=i-m;return [j,...map(j)];});
const ax2=rows(70,j=>weight(j*j,72)),ax3=rows(60,k=>weight(11*k*k,578));
assert(31*31>=70*11&&71*71>=70*72&&11*61*61>=70*578,'70-bit geometric tails');
assert(63>=11&&143>=72&&11*123>=578,'tail ratios at most one half');
assert(3*4*(73+2*72)*142**2<2**30,'joint tail below 2^-40');
const results=[];
let checkedPoints=0;
for(const d of [0,1]){
 let ax1=rows(15,i=>weight((2*i+d)**2,11));
 let Zlo=0n,Zhi=0n,Nlo=0n,Nhi=0n;
 for(const [i,a,b] of ax1) for(const [j,c,e] of ax2){
   const l=a*c,h=b*e;
   for(const [k,u,v] of ax3){
     const f=BigInt(Math.max(Math.abs(204*(2*i+d)+187*j+198*k),Math.abs(204*(2*i+d)-187*j+198*k),Math.abs(612*(2*i+d)-132*k)));
     const w=l*u,z=h*v;
     Zlo+=w;Zhi+=z;Nlo+=w*f;Nhi+=z*f;checkedPoints++;
   }
 }
 Zhi+=P>>40n;Nhi+=C*(P>>40n);
 results.push({Zlo,Zhi,Nlo,Nhi});
}
const [a,b]=results;
// N is scaled by C*P and Z by P. This comparison uses exact big integers.
assert(1000n*(a.Nlo*b.Zlo-b.Nhi*a.Zhi)>C*a.Zhi*b.Zlo,'certified gap exceeds 0.001');
const cut=100_000_000n;
const intervals=results.map(x=>[Number(cut*x.Nlo/(C*x.Zhi)),Number(ceilDiv(cut*x.Nhi,C*x.Zlo))]);
console.log(JSON.stringify({checkedPoints,intervals,intervalDivisor:Number(cut),exactGapOver:0.001}));
