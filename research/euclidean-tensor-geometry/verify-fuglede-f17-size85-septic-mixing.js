'use strict';
function parts(n,s,l,h,a,cb){
 if(!n){if(!s)cb(a);return;}
 for(let v=l;v<=h&&v*n<=s;v++)parts(n-1,s-v,v,h,[...a,v],cb);
}
const Sq=a=>a.reduce((s,v)=>s+v*v,0), require=(x,m)=>{if(!x)throw Error(m)};
for(const [R,cap,bound] of [[6,19,284],[6,8,200],[7,6,156],[7,21,452]]){
 let max=0;
 for(let b=6;b<=18;b++){
  const min=({4:4,5:3,6:2,7:1})[Math.min(R,b-2)];
  parts(b,30,min,cap,[],a=>{max=Math.max(max,Sq(a))});
 }
 require(max<=bound,'local squared envelope');
 console.log({R,cap,max,bound});
}
const p=17n,Q=307n,W=710n,C=30n;
const ceil=(a,b)=>(a+b-1n)/b;
require(ceil(9n*W-27n*19n,C)===196n&&ceil(9n*W-27n*21n,C)===195n,'support');
for(const [N,times3] of [[196n,16468n],[203n,19068n]]){
 const D=p*Q*(Q-N), L=W*W*p*(Q-N)+(18n*W-C*Q)**2n*N;
 require(3n*L>times3*D,'weighted mixing');
 console.log({N:Number(N),gap:(3n*L-times3*D).toString()});
}
let tested=0,minGap=null;
for(let N=195n;N<=202n;N++)for(let M=N;M<=202n;M++){
 const caps=[9n*M+30n*N-5850n,9n*N+30n*M-5850n];
 const E=caps[0]<caps[1]?caps[0]:caps[1],Z=18n*N*M-Q*E;
 const gap=Z*Z-p*N*M*(Q-N)*(Q-M);
 require(Z>0n&&gap>0n,'unweighted mixing');
 if(minGap===null||gap<minGap)minGap=gap;
 tested++;
}
require(tested===36,'support pair count');
console.log({tested,minGap:minGap.toString()});
