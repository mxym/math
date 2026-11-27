'use strict';
const p=17n,Q=307n,W=429n,C=21n;
const check=(x,m)=>{if(!x)throw Error(m)};
let S=0;
function parts(b,t,lo,v){
 if(!b){if(!t)S=Math.max(S,v);return;}
 for(let a=lo;a<=6&&a*b<=t;a++)parts(b-1,t-a,a,v+a*a);
}
for(let b=10;b<=18;b++)parts(b,21,1,0);
check(S===83,'local square envelope');
const ceil=(a,b)=>(a+b-1n)/b;
check(ceil(10n*W,C)===205n,'support lower bound');
const indicatorGap=n=>C*(W*W*p*(Q-n)+(18n*W-Q*C)**2n*n)-83n*W*p*Q*(Q-n);
check(indicatorGap(239n)<=0n&&indicatorGap(240n)>0n,'support upper bound');
let count=0,minGap=null;
for(let n=205n;n<=239n;n++)for(let m=n;m<=239n;m++){
 const a=10n*m+C*n-10n*W,b=10n*n+C*m-10n*W,E=a<b?a:b;
 const t=18n*n*m-Q*E,g=t*t-p*n*m*(Q-n)*(Q-m);
 check(t>0n&&g>0n,'unweighted polarity obstruction');
 minGap=minGap===null||g<minGap?g:minGap;
 count++;
}
check(count===630&&minGap===500548457n,'integer certificate counters');
console.log({S,support:[205,239],count,minGap:minGap.toString()});
