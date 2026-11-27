'use strict';
// Exact extra deficit s=8 for the near-antipodal theorem.
// Number arithmetic is on integers <2^53; quartics and final comparisons use BigInt.
const D=65536,D2=D*D,Q=BigInt(D),Q3=Q**3n,Q4=Q**4n;
const den=2000n*Q4, gam=18n*Q4;
const assert=(v,msg)=>{if(!v)throw Error(msg);};
const min=(a,b)=>a<b?a:b;
const max=(a,b)=>a>b?a:b;
const P=x=>x*(500n*x+245n*Q)*(4n*x*x-Q*Q)+36n*x*Q3;
const F=Array.from({length:D+1},(_,i)=>P(BigInt(i-D/2)));
const E=Array.from({length:D/2+1},(_,i)=>P(-BigInt(i+D/2)));
for(let i=0n;100n*i<=49n*Q;i++){
 const upper=5n*(i+1n)*(49n*Q-100n*i)*(Q*Q-4n*i*i)-36n*i*Q3;
 assert(upper<=gam,'nonedge');
}
function cap(k,c,bound=D){
 const S=[[Array(k).fill(D/2),Array(k).fill(bound)]];
 let n=0;
 while(S.length){
   const [a,b]=S.pop();n++;
   for(let i=k-1;i>0;i--)a[i-1]=Math.max(a[i-1],a[i]);
   for(let i=1;i<k;i++)b[i]=Math.min(b[i],b[i-1]);
   if(a.some((x,i)=>x>b[i])) continue;
   let s=0,z=0,bad=false;
   for(let i=0;i<k;i++){
     s+=a[i];z+=a[i]*a[i];
     if((i+2)*a[i]>=s&&2*((i+2)*z-s*s)>(i+2)*D2){bad=true;break;}
   }
   if(bad)continue;
   if(1000n*b.reduce((s,x,i)=>s+max(E[x-D/2],E[a[i]-D/2]),0n)<=BigInt(c)*den)continue;
   let i=0;for(let j=1;j<k;j++)if(b[j]-a[j]>b[i]-a[i])i=j;
   assert(b[i]-a[i]>1,'uncertified cap box');
   const A=a.slice(),B=b.slice();
   A[i]=B[i]=(a[i]+b[i])>>1;
   S.push([A,b.slice()],[a.slice(),B]);
 }
 return n;
}
function pair(Rn,Rd,c){
 const S=[[-D/2,D/2,-D/2,D/2]];
 let n=0;
 while(S.length){
   const [a,b,j,k]=S.pop();n++;
   if(Rd*(a+j)>Rn*D||Rd*(b+k)<-Rn*D) continue;
   // |F'|<=2 on the nonedge interval.
   const U=(a,b)=>min(gam,min(F[a+D/2],F[b+D/2])+4000n*BigInt(b-a)*Q3);
   if(10000n*(U(a,b)+U(j,k))<=BigInt(c)*den)continue;
   assert(Math.max(b-a,k-j)>1,'uncertified paired nonedge box');
   if(b-a>=k-j){const m=(a+b)>>1;S.push([a,m,j,k],[m,b,j,k]);}
   else{const m=(j+k)>>1;S.push([a,b,j,m],[a,b,m,k]);}
 }
 return n;
}
const B=[356,347,350,358,367,377,386];
const quiet=Array.from(B);quiet[0]=332;quiet[1]=340;
const medium=Array.from(B);medium[0]=340;
const capRuns=[...B.map((c,i)=>[i+2,c,1000]),[2,332,978],[3,340,978],[2,340,985]];
for(const [d,c,x] of capRuns){
 const n=cap(d,c,Math.ceil(x*D/1000));
 console.log({d,c,x,n});
}
const m=pair(21,100,157),s=pair(7,40,140);
assert(m===253359&&s===331699,'paired trees');
console.log({mediumPairBoxes:m,strongPairBoxes:s});
const q=17;
for(let d=2;d<=8;d++) {
 assert(2*(10*quiet[d-2]+(q-1-d)*90)<9165,'unpaired row');
 for(let e=d;e<=8;e++) for(const [a,save] of [[medium,23],[B,40]]){
   assert(10*(a[d-2]+a[e-2])+(2*(q-1)-d-e)*90-(q-d-e)*save<9165,'paired row');
 }
}
console.log('exact pass: deficit 8');
