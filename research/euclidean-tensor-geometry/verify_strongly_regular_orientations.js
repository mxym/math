// Exact integer parameter audit; all operands fit in the safe Number range.
'use strict';
function gcd(a,b){return b ? gcd(b,a%b) : a;}
const survivors=[];
let tested=0;
for(let n=3;n<=2210;n++){
 const d=Math.floor((5*n+15)/16);
 for(let k=2*d;k<n-1;k++){
  const ell=n-k-1;
  if(40*(d-ell)>7*k) continue;
  const step=k/gcd(k,ell);
  for(let mu=step;mu<k;mu+=step){
   const L=k-1-ell*mu/k;
   const D=(L-mu)**2+4*(k-mu);
   const w=Math.floor(Math.sqrt(D));
   if(w*w!==D || (L-mu+w)%2) continue;
   const r=(L-mu+w)/2,s=(L-mu-w)/2;
   const numerator=-k-(n-1)*s, denominator=r-s;
   if(r<=0 || numerator%denominator) continue;
   const f=numerator/denominator,g=n-1-f;
   if(f<=0 || g<=0 || 2*n>f*(f+3)) continue;
   tested++;
   if(n*(L-3*r)<=3*(k-r)*(k-2*d)) survivors.push([n,k,L,mu,r,s,f,g]);
  }
 }
}
if(tested!==1932||JSON.stringify(survivors)!=='[[16,10,6,6,2,-2,5,10]]') throw Error('parameter audit mismatch');
console.log({tested,survivors});
