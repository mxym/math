'use strict';
// Fixed synthetic theta and lattice examples only.
let exact=0,numeric=0;
function check(ok,msg){if(!ok)throw Error(msg);exact++;}
function near(x,y,e,msg){if(!Number.isFinite(x)||!Number.isFinite(y)||Math.abs(x-y)>e)throw Error(msg+': '+x+' vs '+y);numeric++;}
function le(x,y,e,msg){if(!Number.isFinite(x)||!Number.isFinite(y)||x>y+e)throw Error(msg+': '+x+' > '+y);numeric++;}
let state=0xd33b028a;
function gen(k){state=(Math.imul(1664525,state)+1013904223)>>>0;return (state>>>8)%k;}
const sq=x=>x*x;
const circle=x=>x-Math.round(x);
const ga=(a,x)=>Math.exp(-a*x*x);
const phase=(a,x)=>ga(a,circle(x));
function theta(a,x){
 x=circle(x);
 if(a<=4){
  let r=1;
  for(let k=1;k<12;k++)r+=2*Math.exp(-Math.PI*Math.PI*k*k/a)*Math.cos(2*Math.PI*k*x);
  return Math.sqrt(Math.PI/a)*r;
 }
 let r=0,T=2+Math.ceil(Math.sqrt(52/a));
 for(let k=-T;k<=T;k++)r+=ga(a,k+x);
 return r;
}
function oddRatio(a,x){
 let c=0,s=0;
 for(let k=1;k<65;k+=2){
   const w=Math.exp(-Math.PI*Math.PI*(k*k-1)/a);
   c+=w*Math.cos(2*Math.PI*k*x);s+=w;
 }
 return c/s;
}

// Exact unimodal-sequence telescoping and finite phase-support combinatorics.
for(let run=0;run<3900;run++){
  const n=3+gen(45),j=gen(n),a=Array(n).fill(0);a[j]=2+gen(20000);
  for(let i=j-1;i>=0;i--)a[i]=gen(a[i+1]+1);
  for(let i=j+1;i<n;i++)a[i]=gen(a[i-1]+1);
  let q=0;
  for(let i=0;i<=n;i++)q+=Math.abs((a[i]||0)-(a[i-1]||0));
  check(q===2*a[j],'unimodal one-step shift telescopes');
  const d=1+gen(25), k=gen(400);
  let allowed=0;
  for(let i=0;i<d;i++)allowed+=(k*i)%d===0?1:0;
  check(allowed===gcd(d,k),'exact character subgroup count');
}
function gcd(a,b){return b?gcd(b,a%b):a;}

// Endpoint-normalized Fourier chord. The odd ratio stays stable as a tends to 0.
for(let i=0;i<=185;i++){
 const a=.095*Math.exp(i/185*Math.log(125/.095));
 const A0=theta(a,0),A1=theta(a,.5),q=ga(a,.5);
 const low=(1+q)/(A0+A1),peak=1/A0;
 const bridge=1-low*A0;
 near(low*A1-bridge,q,6e-15,'exact lower endpoint interpolation');
 le(q/A1,low,6e-15,'centered lower strictly above unrestricted pointwise minimum');
 le(low,peak,6e-15,'ordered extrema');
 for(let j=1;j<100;j++){
   const x=j/200;
   le(low*theta(a,x)+bridge*oddRatio(a,x),phase(a,x),7e-15,'global pointwise chord');
 }
}

// Independently check the derivative ratio and the initial slope majorant.
function slope(a,x,h){
 let f=0,g=0;
 const n=2+Math.ceil(Math.sqrt(70/a));
 for(let k=0;k<=n;k++){
    const j=k+h;if(j===0)continue;
    const z=2*a*j*x,c=Math.exp(-a*j*j)*j;
    f+=c*Math.sinh(z);
    g+=c*(2*a*j)*Math.cosh(z);
 }
 return g/f;
}
for(let j=0;j<=50;j++){
  const a=.3*Math.pow(110/.3,j/50);
  for(let k=1;k<100;k++){
    const x=k/200;
    le(slope(a,x,.5),slope(a,x,0),5e-11,'logarithmic derivative ordering');
  }
}
for(const a of [8,10,15,20,40]){
 let b=0;
 for(let j=3;j<35;j+=2)b+=2*Math.pow(j,4)*Math.exp(-a*sq(j-1)/4);
 le(b,1,0,'initial derivative comparison geometric majorant');
}

// Compare direct lattice TV and affinity with the fiber identities.
for(const t of [.55,1.3,2.6,5,8]){
 for(const d of [1,2,3,5]){
  for(const h of [.24,.69,1.44]){
   for(const shear of [0,.5,.2,1/Math.sqrt(5)]){
    const a=t*t/2,A0=theta(a,0),A1=theta(a,.5),q=ga(a,.5);
    let mass=0,abs=0,aff=0,num=0,den=0,alt=0;
    const range=Math.ceil(12/h);
    for(let k=-range;k<=range;k++){
      const w=Math.exp(-sq(k*h)/2);
      for(let j=0;j<d;j++){
        const x=k*shear+j/d;
        num+=w*phase(a,x);den+=w*theta(a,x);alt+=w*theta(a,x+.5);
      }
      let lo=Math.floor(d*(-(12+t)/t-k*shear)),hi=Math.ceil(d*((12+t)/t-k*shear));
      for(let j=lo;j<=hi;j++){
        const x=j/d+k*shear;
        const u=w*ga(a,x),v=w*ga(a,x-1);
        mass+=u;abs+=Math.abs(u-v);aff+=Math.sqrt(u*v);
      }
    }
    near(abs/(2*mass),num/den,4e-14,'TV ratio vs direct lattice sum');
    near(aff/mass,q*alt/den,4e-14,'Hellinger ratio vs direct lattice sum');
    le((1+q)/(A0+A1),num/den,4e-14,'centered lower envelope');
    le(num/den,1/A0,4e-14,'centered upper envelope');
    le(q*A1/A0,aff/mass,4e-14,'affinity lower envelope');
    le(aff/mass,q,4e-14,'affinity upper envelope');
    if(d===1&&shear===0)near(num/den,1/A0,4e-14,'upper equality lattice');
    if(d===2&&(shear===0||shear===.5))near(num/den,(1+q)/(A0+A1),4e-14,'lower equality lattice');
   }
  }
 }
}
for(const h of [.58,.63,.7,.8,1.0]){
 const v=2*Math.PI*Math.PI/(h*h);
 let n=0,d=0;
 for(let k=-7;k<=7;k++){
   n+=Math.exp(-v*sq(k+.5));
   d+=Math.exp(-v*sq(k));
 }
 near((n/d)/(2*Math.exp(-v/4)),1,8e-9,'primitive lower endpoint imbalance');
}
console.log({exact_checks:exact,numerical_checks:numeric});
