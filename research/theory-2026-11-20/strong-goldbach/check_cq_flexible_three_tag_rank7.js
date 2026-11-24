"use strict";
// Directed outward capacity, then directed inward forward pairing.
{

const G=4000n,Q=10n**14n;
const cu=(a,b)=>(a+b-1n)/b;
const max=(a,b)=>a>b?a:b;
let U2=0n,U3=0n;
for(let t=160n;t<420n;t++){
 for(let v=680n;t+4n*v<G;v++){
   const x=G-t-v, e=1996n-t-v-2n;
   U2+=cu(3840n*x**3n*Q,27n*e*G**4n);
 }
 for(let v=t;t+6n*v<G;v++){
  for(let w=v;t+v+5n*w<G;w++){
   const x=G-t-v-w, e=1996n-t-v-w-3n;
   U3+=cu(960n*x*x*max(3n*w,e)*Q,e*3n*w*G**4n);
  }
 }
}
if(U2+U3>=1672n*Q/1000n)throw Error("D0 capacity");
console.log(JSON.stringify({U2:String(U2),U3:String(U3),total:String(U2+U3),cap:Number(U2+U3)/Number(Q)}));
}
{

const G=10000n,h=20n,tick=10n**16n,mn=969075913n,md=7200000000n;
const min=(a,b)=>a<=b?a:b,max=(a,b)=>a>=b?a:b;
let sum=0n,all=0,kept=0,rankForced=[0,0,0],split=[0,0,0,0,0,0,0,0],oldCells=0,newCells=0,nrSum=0n;
for(let t0=20n;t0<400n;t0+=h)for(let v0=t0+h;v0<1700n;v0+=h)for(let w0=v0+h;w0<2000n;w0+=h){
 const t1=t0+h,v1=v0+h,w1=w0+h,S0=t0+v0+w0,S1=t1+v1+w1,X0=G-S1,X1=G-S0;
 if(S1>4900n||5n*w1>G-t1-v1)continue;
 let best=0n,bestRank=-1,bestMask=-1;let old=false;
 for(let mask=1;mask<8;mask++){
  const q0=(mask&1?t0:0n)+(mask&2?v0:0n)+(mask&4?w0:0n);
  const q1=q0+BigInt((mask&1?1:0)+(mask&2?1:0)+(mask&4?1:0))*h;
  const B=4990n+q0/2n,E=B-S1;
  if(E<=S1-q1 || 32n*(2n*B+3n*q1)+7n*G>=32n*19970n ||
    16n*(2n*B+3n*q1)+7n*(B-q0-q1)>=16n*19970n ||
    (2n*B-q1)>9990n)continue;
  if(mask===6&&v0<=1000n&&w0<=1400n&&S1<=2600n)old=true;
  for(let j=1n;j<=40n;j++){
   const z=E/2n-5n*j;
   if(z<=w1|| 5n*z<=X1 || E>=4n*z)continue;
   const fN=mn*4n*(E-2n*z)*G,fD=md*E*E;
   const rN=1672n*max(0n,X1-4n*z)**3n*G,rD=1000n*144n*z**4n;
   const n=fN*rD-rN*fD,d=fD*rD;
   if(n<=0n)continue;
   const k4=96n*(4n*G*G-10n*S1*G+5n*S1*S1)*G;
   const k5=1920n*z*(X0-z)*G,k6=3840n*z*z*(X0-2n*z);
   const K=min(k4,min(k5,k6));
   if(K<=0n)continue;
   const val=n*K*t0*v0*w0*(2n*h)**3n*tick/
            (d*G**6n*(2n*t0+h)*(2n*v0+h)*(2n*w0+h));
   if(val>best){best=val;bestRank=(K===k4?0:K===k5?1:2);bestMask=mask;}
  }
 }
 if(best>0n){kept++;rankForced[bestRank]++;sum+=best;split[bestMask]++;if(old)oldCells++;else{newCells++;nrSum+=best;}}
}
if(kept!==40604 || newCells!==15885 || sum!==15946942064146n || nrSum!==3535297371491n)throw Error("cell certificate");
console.log(JSON.stringify({actualPositiveCells:kept,chosenMinimumRanks:rankForced,split,oldCells,newCells,newOnly:String(nrSum),sumTicks:String(sum),marginalExcess:Number(sum)/Number(tick)}));
}
