"use strict";
const G=10000n,h=20n,tick=10n**16n,mn=969075913n,md=7200000000n;
const min=(a,b)=>a<=b?a:b,max=(a,b)=>a>=b?a:b;
const pow=(a,n)=>a**n;
let sum=0n,all=0,kept=0,reverseBad=0,rankForced=[0,0,0],maxrate=0n;
for(let t0=20n;t0<400n;t0+=h)for(let v0=t0+h;v0<=1000n;v0+=h)for(let w0=v0+h;w0<=1400n;w0+=h){
 const t1=t0+h,v1=v0+h,w1=w0+h,S0=t0+v0+w0,S1=t1+v1+w1,X0=G-S1,X1=G-S0;
 if(S1>2600n||5n*w1>G-t1-v1)continue;
 const q0=v0+w0,q1=v1+w1,B=4990n+q0/2n,E=B-S1;
 if(E<=0n || 32n*(2n*B+3n*q1)+7n*G>=32n*19970n ||
    16n*(2n*B+3n*q1)+7n*(B-q0-q1)>=16n*19970n)continue;
 all++;
 let best=0n,bestRank=-1;
 for(let j=1n;j<=40n;j++){
  const z=E/2n-5n*j;
  if(z<=w1|| 5n*z<=X1 || E>=4n*z)continue;
  const fN=mn*4n*(E-2n*z)*G,fD=md*E*E;
  const rN=4909n*max(0n,X1-4n*z)**3n*G,rD=1000n*144n*z**4n;
  const n=fN*rD-rN*fD,d=fD*rD;
  if(n<=0n)continue;
  const k4=384n*(G*G-5n*S1*G+5n*S1*S1)*G;
  const k5=1920n*z*(X0-z)*G,k6=3840n*z*z*(X0-2n*z);
  const K=min(k4,min(k5,k6));
  if(K<=0n)continue;
  const val=n*K*t0*v0*w0*(2n*h)**3n*tick/
            (d*G**6n*(2n*t0+h)*(2n*v0+h)*(2n*w0+h));
  if(val>best){best=val;bestRank=(K===k4?0:K===k5?1:2);}
 }
 if(best>0n){kept++;rankForced[bestRank]++;sum+=best;}
 if(best>maxrate)maxrate=best;
}
if(sum*100000n<=90n*tick)throw Error("new actual wrong-rank subtraction floor");
console.log(JSON.stringify({actualPositiveCells:kept,candidates:all,chosenMinimumRanks:rankForced,sumTicks:String(sum),marginalExcess:Number(sum)/Number(tick)}));
