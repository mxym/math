'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),mod=x=>(x%p+p)%p;
const power=R.map(x=>R.slice(0,8).map(d=>x**d%p));
const gcd=(a,b)=>b?gcd(b,a%b):a;
const expected6=['2,0,1,0,2,0,1','6,0,13,0,12,0,3'].sort();
const expected7=['6,16,0,8,14,6,0,1','2,1,0,7,0,7,0,1','1,13,0,10,0,11,0,1','3,0,9,3,8,12,0,1','0,6,4,15,13,12,0,1'].sort();
for(let d=2;d<=7;d++){
 const a=new Uint8Array(d+1),H=new Uint8Array(17),classes=gcd(d,16),reps=[];
 let lifts=0;
 function rec(j){
  if(j<d-1){for(let u of R){a[j]=u;rec(j+1);}return;}
  H.fill(0);let total=0;
  for(const t of R){let y=0;for(let k=1;k<=d;k++)y+=power[t][k]*a[k];y%=p;H[y]++;total+=y;}
  for(const c of R){
   const lc=(34-total)/p,zeros=H[(17-c)%p];
   if(Number.isInteger(lc)&&lc>=0&&lc<=zeros){
    if(lc)lifts++;const b=Array.from(a);b[0]=c;reps.push(b.join(','));
   }
   total+=p-p*H[16-c];
  }
 }
 for(let i=0;i<classes;i++){a[d]=3**i%p;rec(1);}
 const expected=d===6?expected6:d===7?expected7:[];
 if(lifts||JSON.stringify(reps.sort())!==JSON.stringify(expected))throw Error('normalized degree '+d+' catalogue');
 console.log({degree:d,normalizedCount:reps.length,centeredCount:reps.length*16/classes,lifts});
}
