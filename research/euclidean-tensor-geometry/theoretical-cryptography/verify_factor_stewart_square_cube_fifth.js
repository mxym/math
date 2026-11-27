"use strict";
// Exact finite checks of the displayed polynomial and integer intervals.
// This is not a numerical test of Weyl's theorem.
let checks=0;
function test(x,why){++checks;if(!x)throw Error(why);}
function sqrt(n){
  if(n<2n)return n;
  let x=1n<<BigInt((n.toString(2).length+1)>>1);
  for(;;){const y=(x+n/x)>>1n;if(y>=x)return x;x=y;}
}
function gcd(a,b){for(;b;)[a,b]=[b,a%b];return a;}
function mul(a,b){
  const c=Array(a.length+b.length-1).fill(0n);
  for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]+=a[i]*b[j];
  return c;
}
function pow(a,k){let r=[1n];for(let i=0;i<k;i++)r=mul(r,a);return r;}
const A=mul([0n,1n],pow([3n,125n],5)), B=pow([1n,125n,3125n],3);
const E=[1n,132n,5625n,78125n,0n,0n,0n];
for(let j=0;j<E.length;j++)test(B[j]-A[j]===E[j],"exact polynomial coefficient");
let previous=0n, successful=0, belowFifth=0, aboveThreeTenths=0, first=[];
const V=6250000n, V2=V*V;
for(let n=1n;n<=40000n;n++){
  const t=n**5n, a=n*(125n*t+3n), b=3125n*t*t+125n*t+1n;
  const F=a**5n,C=b**3n,D=C-F,q=sqrt(F),Q=q*q;
  test(D===78125n*t**3n+5625n*t*t+132n*t+1n,"gap identity");
  test(0n<D&&Q<=F&&F<(q+1n)**2n,"order and floor");
  test(Q>previous,"injective square starts");
  previous=Q;
  test(gcd(a,b)===1n,"cube and fifth-power bases are coprime");
  test(11n*q<25n*D&&50n*D<23n*q,"0.44 < D/q < 0.46");
  const U=78125n*(V*t**3n+375000n*t*t+6750n*t+27n);
  const twoSquares=5n*U*U-V2*F;
  test(0n<twoSquares&&twoSquares*t<2n*q*V2,"0 < polynomial minus exact root < n^-5");
  const ok=Q<F&&C<=Q+q;
  if(ok){++successful;if(first.length<5)first.push({n:String(n),N:String(Q)});}
  if(Q<F&&25n*F<=(5n*q+1n)**2n){
    ++belowFifth;
    test(ok,"small fractional part implies a valid interval");
  }
  if(100n*F>=(10n*q+3n)**2n){
    ++aboveThreeTenths;
    test(!ok,"large fractional part excludes this square start");
  }
}
test(successful>0&&belowFifth>0&&aboveThreeTenths>0,"both decisions exercised");
console.log({checks,parameters:40000,successful,belowFifth,aboveThreeTenths,first});
