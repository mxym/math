"use strict";
// Exhaustive small field point counts only. There is no factoring procedure.
const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){[a,b]=[b,a%b];}return a;};
function rat(n,d=1n){n=BigInt(n);d=BigInt(d);if(d<=0n)throw Error("denominator");const c=gcd(n,d);return [n/c,d/c];}
const add=([a,b],[c,d])=>rat(a*d+b*c,b*d), mul=([a,b],[c,d])=>rat(a*c,b*d);
const le=([a,b],[c,d])=>a*d<=b*c, eq=(x,y)=>le(x,y)&&le(y,x);
const mod=(a,p)=>(a%p+p)%p;
const pow=(x,n,p)=>{let y=1;while(n){if(n%2)y=y*x%p;x=x*x%p;n=Math.floor(n/2);}return y;};
function phi(n){let k=0;for(let r=1;r<=n;r++)k+=Number(gcd(BigInt(r),BigInt(n))===1n);return k;}
let fieldCases=0,poolCases=0,negativeGaps=0,exceptional=0;
for(const [P,S] of [[10,[11,13,17,19]],[16,[17,19,23,29,31]]]){
 const forms=[
  [[1,0],[[7,1],[7,2],[7,9]],[[0,1],[11,0],[520,4]]],
  [[1,-1],[[0,0],[1,1],[6,6]],[[3,1],[0,16],[514,2]]],
  [[1,1],[[6,0],[3,3],[0,6]],[[1,1],[8,0],[33,37]]],
  [[2,3],[[0,4],[3,2],[6,0]],[[1,0],[1,4],[30,7]]],
 ];
 for(const [v,base,tops] of forms)for(const top of tops)for(const A of [1,-4,11,17*19,23])for(const sign of [-1,1]){
  const grade=([a,b])=>v[0]*a+v[1]*b,c=grade(base[0]),g=grade(top)-c;
  if(g===0||base.some(e=>grade(e)!==c)||gcd(BigInt(v[0]),BigInt(v[1]))!==1n)throw Error("bad form");
  const coeff=[2,sign,3*sign];
  const s=S.filter(p=>A%p===0).length,h=2;let sum=rat(0),weightedGcd=rat(0),W=rat(0);
  for(let j=1;j<2*P;j++)if(Math.abs(g)%j===0)W=add(W,rat(phi(j),j));
  const cs=[];
  for(const p of S){
   const val=(x,y)=>mod(A*pow(x,top[0],p)*pow(y,top[1],p)+base.reduce((z,[a,b],i)=>z+coeff[i]*pow(x,a,p)*pow(y,b,p),0),p);
   let torus=0,all=0;for(let x=0;x<p;x++)for(let y=0;y<p;y++){const hit=Number(val(x,y)===0);all+=hit;if(x&&y)torus+=hit;}
   const k=gcd(BigInt(g),BigInt(p-1));
   if(A%p!==0){if(BigInt(torus)>k*BigInt(p-1))throw Error("coset bound");const ub=add(rat(h,p),rat(k,p-1));if(!le(rat(all,p*p),ub))throw Error("field bound");}else exceptional++;
   const z=rat(all,p*p);sum=add(sum,z);cs.push(z);
   weightedGcd=add(weightedGcd,rat(k,p-1));fieldCases++;
  }
  const dBound=mul(rat(3*P,P-1),W);
  if(!le(weightedGcd,dBound)||!le(sum,add(add(rat(s),rat(h*S.length,P)),dBound)))throw Error("pool bound");
  let twice=rat(0),squares=rat(0);for(let i=0;i<cs.length;i++){squares=add(squares,mul(cs[i],cs[i]));for(let j=0;j<i;j++)twice=add(twice,mul(rat(2),mul(cs[i],cs[j])));}
  if(!eq(add(twice,squares),mul(sum,sum)))throw Error("unordered-pair identity");
  poolCases++;if(g<0)negativeGaps++;
 }
}
if(!exceptional||!negativeGaps)throw Error("missing edge case");
console.log({poolCases,fieldCases,negativeGaps,exceptionalCoefficientFieldCases:exceptional});