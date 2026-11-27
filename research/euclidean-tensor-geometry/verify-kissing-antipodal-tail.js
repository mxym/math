'use strict';

// Exact verifier for the two-type weighted quartic bounds.
// Ordinary Number operations below are on integers <2^53; every quartic
// and cross-product of rational bounds uses BigInt.
const D=65536, D2=D*D, Q=BigInt(D), Q3=Q**3n, Q4=Q**4n;
const assert=(ok,msg)=>{if(!ok)throw Error(msg);};
const cases=[
  {s:5,K:20,L:7,U:0,g:[49,6400], degrees:[1,2,3,4,5],
   caps:[490,550,570,580,590], nodes:[1,37,179,1293,51881]},
  {s:6,K:100,L:49,U:0,g:[49,4000], degrees:[2,3,4,5,6],
   caps:[384,396,409,421,433], nodes:[173,433,1627,8537,136533]},
  {s:7,K:500,L:245,U:9,g:[9,1000], degrees:[2,3,4,5,6,7],
   caps:[363,372,381,390,399,408], nodes:[71,207,625,1583,4589,14771]},
];

for(const {s,K,L,U,g,degrees,caps,nodes} of cases){
 const k0=BigInt(K),l0=BigInt(L),u0=BigInt(U);
 const G=BigInt(g[0]),J=BigInt(g[1]);
 const denom=4n*k0*Q4;
 assert(L*2<=K&&L>0&&U>=0,'convexity conditions');
 assert(u0*J<=2n*k0*G,'positive nonedge');
 let intervals=0;
 for(let i=0n;k0*i<=l0*Q;i++){
   // a in [i/D,(i+1)/D] and 0<=a<=lambda; bound all positive
   // factors in a(lambda-a)(1/4-a^2)-mu*a from above, then subtract.
   const upper=(i+1n)*(l0*Q-k0*i)*(Q*Q-4n*i*i)-4n*u0*i*Q3;
   assert(upper*J<=G*denom,'negative nonedge');
   intervals++;
 }
 const E=Array.from({length:1+D/2},(_,i)=>{
   const x=BigInt(i+D/2);
   return x*(k0*x-l0*Q)*(4n*x*x-Q*Q)-4n*u0*x*Q3;
 });

 function boxes(k,cap){
   const limit=BigInt(cap)*denom;
   const S=[[Array(k).fill(D/2),Array(k).fill(D)]];
   let visits=0,rejected=0,accepted=0;
   while(S.length){
     const [a,b]=S.pop();visits++;
     // Restrict to sorted projection coordinates.
     for(let i=k-1;i>0;i--)a[i-1]=Math.max(a[i-1],a[i]);
     for(let i=1;i<k;i++)b[i]=Math.min(b[i],b[i-1]);
     if(a.some((lo,i)=>lo>b[i])){rejected++;continue;}

     let sum=0,sumsq=0,fail=false;
     for(let i=0;i<k;i++){
       sum+=a[i];sumsq+=a[i]*a[i];
       const j=i+1;
       // For the prefix lower endpoints, C_j^{-1}a is nonnegative
       // exactly if (j+1)a_last >= sum. This supplies a nonnegative
       // separating weight if the squared C_j^{-1} norm exceeds 1.
       if((j+1)*a[i]>=sum && 2*((j+1)*sumsq-sum*sum)>(j+1)*D2){
         fail=true;break;
       }
     }
     if(fail){rejected++;continue;}

     // F(-t) is convex for 1/2<=t<=1, since
     // 12t^2-1/2-6lambda*t>=1 at and above t=1/2.
     let total=0n;
     for(let i=0;i<k;i++){
       const lo=E[a[i]-D/2],hi=E[b[i]-D/2];
       total+=lo>hi?lo:hi;
     }
     if(1000n*total<=limit){accepted++;continue;}

     let j=0;
     for(let i=1;i<k;i++)if(b[i]-a[i]>b[j]-a[j])j=i;
     assert(b[j]-a[j]>1,'uncertified unit-grid box');
     const lower=a.slice(),upper=b.slice();
     lower[j]=upper[j]=(a[j]+b[j])>>1;
     S.push([lower,b.slice()],[a.slice(),upper]);
   }
   return {visits,rejected,accepted};
 }

 for(let i=0;i<degrees.length;i++){
   const d=degrees[i],cap=caps[i];
   const count=boxes(d,cap);
   assert(count.visits===nodes[i],'box replay counts');
   // cap/1000+(2s-d)*g < 3/4*(1+1/s-lambda)-mu.
   const left=BigInt(cap)*J+1000n*BigInt(2*s-d)*G;
   const right=3n*(BigInt(s+1)*k0-BigInt(s)*l0)-4n*BigInt(s)*u0;
   assert(left*4n*BigInt(s)*k0 < right*1000n*J,'row threshold');
   console.log({s,d,cap:cap+'/1000',...count});
 }
 if(s===5){
   // Degree zero also allowed in s=5; later induction excludes <=1.
   const right=3n*(BigInt(s+1)*k0-BigInt(s)*l0)-4n*BigInt(s)*u0;
   assert(BigInt(2*s)*G*4n*BigInt(s)*k0 < right*J,'zero-degree row threshold');
 }
 console.log({s,intervals,nonedge:g.join('/'),status:'exact pass'});
}
