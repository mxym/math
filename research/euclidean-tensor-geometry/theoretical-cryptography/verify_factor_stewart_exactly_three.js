"use strict";
// Fixed finite verification of the supplement. The asymptotic uses a proof.
let checks=0;
function test(x,why){++checks;if(!x)throw Error(why);}
function root(x,e){
  let lo=0n,hi=1n<<BigInt(Math.ceil(x.toString(2).length/e));
  e=BigInt(e);
  while(hi-lo>1n){const m=(hi+lo)>>1n;if(m**e<=x)lo=m;else hi=m;}
  test(lo**e<=x&&(lo+1n)**e>x,"root bracket");
  return lo;
}
const isPrime=p=>{for(let d=2;d*d<=p;d++)if(p%d===0)return false;return p>=2;};
function hits(lo,hi,e){
  let r=root(lo,e);
  if(r**BigInt(e)<lo)++r;
  const out=[];
  for(;r**BigInt(e)<=hi;r++)out.push(r**BigInt(e));
  return out;
}
let old=-1n,success=0,exact=0,wideEvents=0;
for(let n=1n;n<=2500n;n++){
  const t=n**5n,a=n*(125n*t+3n),b=3125n*t*t+125n*t+1n;
  const F=a**5n,C=b**3n,q=root(F,2),lo=q*q,hi=lo+q;
  test(old<lo,"disjoint finite intervals");old=hi;
  const powers=new Set();
  const exmax=hi.toString(2).length-1;
  let highHit=false;
  for(let e=2;e<=exmax;e++)if(isPrime(e)){
    const z=hits(lo,hi,e);
    if(e<=5)test(z.length<=1,"small exponent spacing");
    if(e>=7&&z.length)highHit=true;
    for(const value of z)powers.add(value);
  }
  if(highHit)++wideEvents;
  if(lo<F&&C<=hi){
    ++success;
    test(powers.has(lo)&&powers.has(F)&&powers.has(C),"three exhibited and distinct powers");
    if(!highHit){test(powers.size===3,"no hidden perfect power");++exact;}
  }
}
const fixture=7n**7n;
test(hits(fixture-1n,fixture+1n,7)[0]===fixture,"higher exponent detection");
test(exact>0,"exact-three fixtures exist");
console.log({checks,parameters:2500,success,exact,wideEvents});