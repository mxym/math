"use strict";
// Directed certificate for the whole parameter rectangle. All comparisons BigInt.
const Q=(n,d=1n)=>[BigInt(n),BigInt(d)];
const ad=([n,d],[m,k])=>[n*k+m*d,d*k];
const su=([n,d],[m,k])=>[n*k-m*d,d*k];
const mu=([n,d],[m,k])=>[n*m,d*k];
const di=([n,d],[m,k])=>[n*k,d*m];
const lt=([n,d],[m,k])=>n*k<m*d;
const mn=(a,b)=>lt(a,b)?a:b;
const flo=([n,d])=>n/d, ceil=([n,d])=>(n+d-1n)/d;
const scale=Q(1000000000),unit=Q(1,2000);
function lupper(n,d) {
 const u=Q(n-d,n+d),u2=mu(u,u); let v=u,sum=Q(0);
 for(let j=0;j<14;j++){sum=ad(sum,di(v,Q(2*j+1)));v=mu(v,u2);}
 return mu(Q(2),ad(sum,di(v,mu(Q(29),su(Q(1),u2)))));
}
function certify(level) {
const logs=new Map();
for(let a=60;a<=124;a+=2){for(let k=2*a;k<level-2*a;k++){
 const z=k+1-a;logs.set(a+","+k,lupper(z,a));
}}
function upperCredit(a,b){
 let tot=0n; const mu0=Q(a,2000),beta=Q(b,2000), end=Math.min(level-2*a,2000-2*b);
 for(let k=2*a;k<end;k++){
  const x=Q(k,2000), slack=su(di(su(Q(1),x),beta),Q(2));
  const main=mu(mu(di(Q(281,1000),mu0),di(slack,x)),logs.get(a+","+k));
  tot+=ceil(mu(mu(unit,main),scale));
 } return tot;
}
const floors=[];
for(let k=0;k<1000;k++){
 const x=Q(k,2000);const fa=di(Q(2),mu(su(Q(1,2),x),su(Q(1,2),x)));
 floors[k]=k>=500?fa:mn(fa,di(Q(1),su(Q(1,4),x)));
}
function lowerPenalty(a,b){
 let tot=0n; const beta=Q(b,2000);
 for(let k=a;k<b;k++){
  const y=Q(k+1,2000);
  const main=mu(di(su(Q(1),di(y,beta)),y),floors[k]);
  tot+=flo(mu(mu(unit,main),scale));
 } return tot;
}
let min=20000000000n, coords=[];
for(let a=60;a<124;a+=2) for(let b=770;b<900;b+=2) {
 const base=ceil(mu(scale,mu(su(Q(4),di(Q(1),Q(b+2,2000))),di(Q(281,1000),Q(a,2000)))));
 const gap=lowerPenalty(a+2,b)-upperCredit(a,b)-base;
 if(gap<min){min=gap;coords=[a,b];}
}
if(min<=180000000n) throw Error("gap="+min);
return { level:level/2000, gapTicks:String(min),gridCorner:coords, scale:"1000000000", examples:[60,80,110].map(a=>({mu:a/2000,creditTicks:String(upperCredit(a,800)),penaltyFloorTicks:String(lowerPenalty(a,800))})) };
}
for (const level of [498,500]) console.log(JSON.stringify(certify(level)));
