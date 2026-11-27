"use strict";
// Finite certificate for the elementary part of the #693 note.
let checks=0,anchors=0,intervals=0;
const ok=(x,s)=>{++checks;if(!x)throw Error(s);};
const gcd=(a,b)=>b===0n?a:gcd(b,a%b);
let L=1n;
const has=(m,n)=>{
  for(let d=n+1n;d<2n*n;++d)if(m%d===0n)return true;
  return false;
};
for(let a=3n;a<=9n;++a){
  if(a===3n)L=6n;else L=L*a/gcd(L,a);
  for(let n=2n*a+4n;n<=290n;++n){
    const lo=a*n+1n,hi=a*n+n/2n;
    for(let x=((lo+L-1n)/L)*L;x<=hi;x+=L){
      ok(x/a>n&&x/a<2n*n&&x%a===0n,"anchor quotient witness");
      ok(has(x,n),"anchor is admissible");
      for(let t=1n;t<=a/2n;++t)ok(!has(x+t,n),"internal run strictly empty");
      const r=x+a/2n+1n,w=((r+n)/(n+1n))*(n+1n);
      ok(r<=w&&w<n*n&&has(w,n),"right admissible endpoint");
      ++anchors;
    }
  }
}
for(let n=3n;n<=31n;++n){
  for(let x=n;x<=n*n;x+=3n){
    const H=19n+(x%13n);
    let a=0n,b=0n;
    for(let d=n+1n;d<2n*n;++d)a+=(x+H)/d-x/d;
    for(let m=x+1n;m<=x+H;++m)
      for(let d=n+1n;d<2n*n;++d)if(m%d===0n)++b;
    ok(a===b,"two representations of the same local multiplicity");
    ++intervals;
    if(x>=2n*n+2n){
      const q=(x+2n*n-2n)/(2n*n-1n),d=(x+q-1n)/q;
      ok(n<d&&d<2n*n&&q*d>=x&&q*d-x<q,"small-start rounding identity");
    }
  }
}
ok(16n*(84n+13n)===(84n-55n-13n)*97n,"Bourgain exponent");
ok(16n*(194n+13n)===(194n-152n-2n*13n)*207n,"A-process exponent");
for(let r=5n;r<=500n;++r){
  ok(2n*(r-2n)>=r,"last derivative term at least as strong as middle");
  const a=r*r-r+1n,b=r*(r*r*r-3n*r+4n)-(r*r-r+2n)*a;
  ok(b===(r-1n)*(2n*r-1n)*(r-2n)&&b>0n,"strict comparison of the two savings");
}
console.log({checks,anchors,intervals});
