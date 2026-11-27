"use strict";
// Algebraic mixture checks and scalar Gaussian illustrations only.
let exact=0, numeric=0;
function check(ok,msg,fp=false){
  if(!ok)throw Error(msg);
  if(fp)++numeric;else ++exact;
}
function gcd(x,y){x=x<0n?-x:x;y=y<0n?-y:y;while(y)[x,y]=[y,x%y];return x;}
function Fr(x,y=1n){x=BigInt(x);y=BigInt(y);const g=gcd(x,y);return [x/g,y/g];}
function plus(a,b){return Fr(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);}
function mul(a,b){return Fr(a[0]*b[0],a[1]*b[1]);}
function div(a,b){return Fr(a[0]*b[1],a[1]*b[0]);}
function sub(a,b){return plus(a,[-b[0],b[1]]);}
function pow(a,m){return Fr(a[0]**BigInt(m),a[1]**BigInt(m));}
function equal(a,b){return a[0]===b[0]&&a[1]===b[1];}
const one=Fr(1n),zero=Fr(0n);
function mix(f,W){return W.reduce((s,w,i)=>plus(s,mul(w,f[i])),zero);}
for(let Q=2;Q<=22;++Q)for(let m=1;m<=24;++m)
for(let start=0;start<=Q;++start){
  const W=[Fr(1,2),Fr(1,3),Fr(1,6)];
  const R=[start,(3*start+1)%(Q+1),(5*start+2)%(Q+1)].map(u=>Fr(u,Q));
  const p=mix(R,W);if(!p[0])continue;
  const S=R.map(r=>sub(one,pow(sub(one,r),m)));
  const sized=R.map((r,i)=>div(mul(W[i],r),p));
  const soft=R.map(r=>{
    let h=zero,a=one;
    for(let j=0;j<m;++j){h=plus(h,a);a=mul(a,sub(one,r));}
    return div(h,Fr(m));
  });
  check(equal(div(mix(S,W),mul(Fr(m),p)),mix(soft,sized)),"size-biased identity");
  for(let i=0;i<R.length;++i)
    check(equal(S[i],mul(mul(Fr(m),R[i]),soft[i])),"geometric-sum identity");
}
const phi=x=>Math.exp(-x*x/2)/Math.sqrt(2*Math.PI);
function tail(x){
  if(x<0)return 1-tail(-x);
  if(x>=3){
    let h=0;
    for(let k=140;k>=1;--k)h=k/(x+h);
    return phi(x)/(x+h);
  }
  let term=x,sum=x;
  for(let k=1;k<=64;++k){term*=-(x*x)/(2*k);sum+=term/(2*k+1);}
  return 0.5-sum/Math.sqrt(2*Math.PI);
}
function simpson(f,a,b,n=12288){
  const d=(b-a)/n;
  let o=f(a)+f(b);
  for(let i=1;i<n;++i)o+=(i%2?4:2)*f(a+i*d);
  return o*d/3;
}
function prob(u,rho,m,success){
  const s=Math.sqrt(1-rho*rho);
  return simpson(x=>{
    const t=tail((u-rho*x)/s), l=m*Math.log1p(-t);
    return phi(x)*(success ? -Math.expm1(l) : Math.exp(l));
  },-38,38);
}
for(const rho of [.15,.6,.82])for(const m of [1,2,9,33,418])
for(const u of [-.5,.001,.8,2.2]){
  const s=Math.sqrt(1-rho*rho);
  const F=prob(u,rho,m,false), S=prob(u,rho,m,true);
  check(Math.abs(F+S-1)<5e-12,"conditional integrals sum",true);
  if(m===1)check(Math.abs(S-tail(u))<4e-12,"one-call marginal",true);
  const independentMax=simpson(x=>{
    const tailX=tail(x);
    if(tailX>=1 && m>1)return 0;
    const lm=m===1?0:(m-1)*Math.log1p(-tailX);
    return m*phi(x)*Math.exp(lm)*tail((s*x-u)/rho);
  },-12,14);
  check(Math.abs(independentMax-F)<7e-12,"maximum-density representation",true);
}
function gamma(a){
  const coeff=[676.5203681218851,-1259.1392167224028,771.3234287776531,
  -176.6150291621406,12.507343278686905,-.13857109526572012,
  9.984369578019572e-6,1.5056327351493116e-7];
  if(a<.5)return Math.PI/(Math.sin(Math.PI*a)*gamma(1-a));
  const z=a-1,t=z+7.5;
  const v=coeff.reduce((q,c,i)=>q+c/(z+i+1),.9999999999998099);
  return Math.sqrt(2*Math.PI)*Math.pow(t,z+.5)*Math.exp(-t)*v;
}
{
  const rho=.6,s=.8;
  for(const v of [16,22]){
    const m=1/tail(v);
    for(const b of [-.75,0,.75]){
      const u=(v+b)/s, S=prob(u,rho,m,true), ratio=S/(m*tail(u));
      check(Math.abs(ratio-tail(-b/rho))<.054,"cluster-transition illustration",true);
    }
    const d=.6*v, uMinus=s*v-rho*d, alpha=d*s/(rho*v), F=prob(uMinus,rho,m,false);
    check(Math.abs(F/(tail(d)*gamma(1+alpha))-1)<.08,"lower-tail Gamma illustration",true);
    const dd=.31*v,uPlus=s*v+rho*dd,beta=dd*s/(rho*v), S=prob(uPlus,rho,m,true);
    check(Math.abs(S/(tail(dd)*gamma(1-beta))-1)<.08,"upper-tail Gamma illustration",true);
  }
}
console.log("Gaussian repetition budgets: "+exact+" exact checks and "+numeric+" floating illustrations passed.");
