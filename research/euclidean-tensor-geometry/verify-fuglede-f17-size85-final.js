'use strict';
// Integer-only verification of the last three weighted/unweighted incidence cases.
const W=710n,C=30n,V=307n,p=17n;
const B=(x,y)=>x<y?x:y;
function ceil(a,b){return (a+b-1n)/b;}
function floor(a,b){return a>=0n?a/b:-ceil(-a,b);}
function envelope(r) {
  let best=0n;const m={4:4n,5:3n,6:2n};
  function parts(n,total,low,S){if(n===0n){if(total===0n&&S>best)best=S;return;}
    for(let t=low;t*n<=total;t++)parts(n-1n,total-t,t,S+t*t);
  }
  for(let b=6;b<=18;b++)parts(BigInt(b),C,m[Math.min(r,b-2)],0n);
  return best;
}
function ind(num,s){const z=18n*W-C*V,D=p*V*(V-num);
 const L=W*W*p*(V-num)+z*z*num;
 return C*L-s*W*D;
}
function check(r,l,h){
 const k=BigInt(r+2),m=BigInt(8-r),a=BigInt([15,17,19][r-4]),delta=BigInt((r-4)*(16-r)),S=envelope(r);
 const lo=ceil(k*W-a*delta,C),hi=BigInt(h);
 if(lo!==BigInt(l)||ind(hi,S)<=0n||ind(hi-1n,S)>0n||r>4&&ind(lo,envelope(r-1))<=0n)throw Error("support interval");
 function edge(n,m0){let e=k*m0-delta+floor(C*n-k*W+a*delta,m);
  return r===4?B(e,7n*m0):e;
 }
 let tries=0,min=null;
 for(let n=lo;n<hi;n++)for(let m0=n;m0<hi;m0++){
  const E=B(edge(n,m0),edge(m0,n)),t=18n*n*m0-V*E;
  const diff=t*t-p*n*(V-n)*m0*(V-m0);
  if(t<=0n||diff<=0n)throw Error("mixed indicator contradiction failed");
  ++tries;if(min===null||diff<min)min=diff;
 }
 console.log({r,local:Number(S),support:[l,h-1],tries,min:min.toString()});
}
check(4,142,159);
check(5,160,171);
check(6,177,208);
