"use strict";
// The inputs are small generated prime-product examples; no factoring routine.
const must=(b,m)=>{if(!b)throw Error(m);};
const choose=(n,k)=>{if(k<0||k>n)return 0;let r=1;for(let i=0;i<k;i++)r=r*(n-i)/(i+1);return Math.round(r);};
const pop=x=>{let d=0;while(x){x&=x-1;d++;}return d;};
const masks=(w,k)=>Array.from({length:2**w},(_,i)=>i).filter(x=>pop(x)===k);
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
let cuts=0,degreeChecks=0,poolEdges=0,hybridCases=0,repeatedMasks=0;
for(let n=4;n<=7;n++){
 const P=2**(n-1),S=Array.from({length:P},(_,i)=>P+i).filter(prime), es=[];
 for(let i=0;i<S.length;i++)for(let j=i+1;j<S.length;j++)es.push([S[i]*S[j],S[i],S[j]]);
 poolEdges+=es.length;
 for(const A of masks(2*n,n)){
  const u=(n-1)-pop(A&(P-1)),v=n-u,lim=2**Math.min(u,v),cnts=new Map();
  for(const [N,p,q] of es)for(const k of [p,q]){
   const tag=(N&A)*P*2+k;
   const c=(cnts.get(tag)||0)+1;cnts.set(tag,c);must(c<=lim,"deterministic label degree");degreeChecks++;
  }
  cuts++;
 }
}
const x=323,y=391,w=10;const ds=x^y, view=masks(w,5).find(j=>(j&ds)===0);
must(ds===(1<<2|1<<6|1<<7)&&view!==undefined&&(x&view)===(y&view),"nonmatching view");
function gcd(a,b){while(b)[a,b]=[b,a%b];return a;}
function add(a,b){const n=a[0]*b[1]+a[1]*b[0],d=a[1]*b[1],g=gcd(n,d);return [n/g,d/g];}
function mul(a,b){const n=a[0]*b[0],d=a[1]*b[1],g=gcd(n,d);return [n/g,d/g];}
for(let w=3;w<=6;w++)for(let seed=0;seed<20;seed++){
 const U=Array.from({length:2**w},(_,i)=>i).filter(x=>(x+seed)%7<1+(seed%6)||(x^seed)%13===0);
 must(U.length,"test support empty");
 for(let J=0;J<2**w;J++){
  let qSum=[0n,1n],supportSum=[0n,1n];
  for(let x=0;x<2**w;x++){
   let h=[1n,1n], qp=[1n,1n];
   for(let i=0;i<w;i++){
    const b=1<<i, prior=(b-1)&((J&b)?J:2**w-1);
    const den=U.filter(y=>(y&prior)===(x&prior)).length, num=U.filter(y=>(y&(prior|b))===(x&(prior|b))).length;
    h=mul(h,den?[BigInt(num),BigInt(den)]:[1n,2n]);
    if(J&b){
     const de=U.filter(y=>(y&(b-1))===(x&(b-1))).length, nu=U.filter(y=>(y&(2*b-1))===(x&(2*b-1))).length;
     qp=mul(qp,de?[BigInt(nu),BigInt(de)]:[1n,2n]);
    }
   }
   qSum=add(qSum,h);
   if(U.includes(x)){
    supportSum=add(supportSum,h);
    const cnt=BigInt(U.filter(y=>(y&J)===(x&J)).length);
    must(h[0]*qp[0]*BigInt(U.length)**2n===h[1]*qp[1]*cnt,"hybrid likelihood identity");
   }
  }
  must(qSum[0]===qSum[1]&&supportSum[0]<=supportSum[1],"hybrid probability");
  hybridCases++;
 }
}
for(let n=2;n<=8;n++){
 const cuts=masks(2*n,n), sums=[0,0],bn=(1<<n)-1;
 for(const J of cuts){
  const unknown=pop(~(J|(J>>n))&bn);
  const counts=new Map();
  for(let x=0;x<2**n;x++){const tag=(x|(x<<n))&J;counts.set(tag,(counts.get(tag)||0)+1);}
  must(Array.from(counts.values()).every(x=>x===2**unknown),"duplication fiber");
  sums[0]+=unknown;sums[1]+=unknown*(unknown-1);repeatedMasks++;
 }
 must(sums[0]===n*choose(2*n-2,n),"first moment");
 must(sums[1]===n*(n-1)*choose(2*n-4,n),"second factorial moment");
}
console.log({cuts,degreeChecks,poolEdges,hybridCases,repeatedMasks});