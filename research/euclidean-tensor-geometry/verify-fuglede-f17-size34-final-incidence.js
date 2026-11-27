'use strict';
const W=287n,C=15n,Q=307n,p=17n,L=255,maxScaled=32,minScaled=8;
const check=(a,b)=>{if(!a)throw Error(b)};
let S=-1;
let dp=new Int32Array(L+1);dp.fill(-1);dp[0]=0;
for(let b=1;b<=18;b++){
 const u=new Int32Array(L+1);u.fill(-1);
 for(let x=0;x<=L;x++)if(dp[x]>=0)for(let a=minScaled;a<=maxScaled&&x+a<=L;a++)u[x+a]=Math.max(u[x+a],dp[x]+a*a);
 dp=u;if(b>=12)S=Math.max(S,dp[L]);
}
check(S===6993,'local scaled squared-weight norm');
const lowerNormGap=N=>{
 const D=p*Q*(Q-N),X=W*W*p*(Q-N)+(18n*W-C*Q)**2n*N;
 return p*p*C*X-BigInt(S)*W*D;
};
check((12n*W+C-1n)/C===230n,'support lower');
check(lowerNormGap(234n)<=0n&&lowerNormGap(235n)>0n,'support upper');
let pairs=0,gap=null;
for(let n=230n;n<=234n;n++)for(let m=n;m<=234n;m++){
 const a=12n*m+(C*n-12n*W)*p/8n,b=12n*n+(C*m-12n*W)*p/8n,E=a<b?a:b;
 const z=18n*n*m-Q*E,g=z*z-p*n*m*(Q-n)*(Q-m);
 check(z>0n&&g>0n,'unweighted polarity');
 pairs++;if(gap===null||g<gap)gap=g;
}
check(pairs===15&&gap===1531336876n,'certificate counters');
console.log({localScaled:S,support:[230,234],pairs,minGap:gap.toString()});
