'use strict';
const ceil=(x,y)=>Math.ceil(x/y),floor=(x,y)=>Math.floor(x/y);
const fail=(b,s)=>{if(!b)throw Error(s)};
const UMax=307-ceil(10*570-16*14,26);
fail(UMax===96,'uniform support upper');
const need=Array(UMax+1).fill(Infinity);
let explored=0;
for(let U=0;U<=UMax;U++){
 for(let h9=0;h9<=8;h9++)for(let h10=0;h10<=8-h9;h10++)for(let h11=0;h11<=8-h9-h10;h11++){
  const K=307-h9-h10-h11;
  const T=18*U-9*h9-10*h10-11*h11;
  const Q=U*(U-1)-12*18*U+42*307-6*h9-12*h10-20*h11;
  const d=h9+2*h10, slack=17*(26*(307-U)-5700)+238*d;
  if(slack<0||T<4*K||T>8*K||Q<0||Q%2)continue;
  for(let a=Math.max(0,5*K-T);a<=K&&6*a<=Q;a++){
   const bLo=Math.max(0,ceil(6*K+Q-T-8*a,3));
   const bHi=Math.min(K-a,Q/2-3*a,floor(7*K-T+Q/2-6*a,3));
   if(bLo>bHi)continue;
   const b=bLo, n8=Q/2-3*a-b, n7=T-6*K-Q+8*a+3*b, n6=K-a-b-n8-n7;
   fail(n6>=0&&n7>=0&&n8>=0,'low line-count reconstruction');
   fail(4*a+5*b+6*n6+7*n7+8*n8===T&&6*a+2*b+2*n8===Q,'moment reconstruction');
   const cost=V=>8*(3*Math.max(0,a+b-V)+Math.max(0,a-V));
   explored++;
   if(cost(UMax)>slack)continue;
   let lo=0,hi=UMax;
   while(lo<hi){const m=(lo+hi)>>1;if(cost(m)<=slack)hi=m;else lo=m+1;}
   need[U]=Math.min(need[U],lo);
  }
 }
}
let pairs=0;
for(let U=0;U<=UMax;U++)for(let V=U;V<=UMax;V++){
 pairs++;
 fail(!(need[U]<=V&&need[V]<=U),'mutually possible uniform-normal supports');
}
console.log({UMax,explored,pairs,thresholds:need.flatMap((z,i)=>Number.isFinite(z)?[[i,z]]:[])});
