"use strict";
// Exact algebra checks for the rate/crossover and Gaussian saturation channel.
let checks=0;
const gcd=(a,b)=>b===0n?(a<0n?-a:a):gcd(b,a%b);
function q(n,d=1n){
  n=BigInt(n);d=BigInt(d);
  if(d<0n){n=-n;d=-d;}
  const g=gcd(n,d);return [n/g,d/g];
}
const add=([a,b],[c,d])=>q(a*d+b*c,b*d);
const neg=([a,b])=>[-a,b];
const sub=(x,y)=>add(x,neg(y));
const mul=([a,b],[c,d])=>q(a*c,b*d);
const div=([a,b],[c,d])=>q(a*d,b*c);
const sq=x=>mul(x,x);
const le=([a,b],[c,d])=>a*d<=c*b;
const str=x=>x.join("/");
function eq(a,b,msg){checks++;if(str(a)!==str(b))throw Error(msg+": "+str(a)+" != "+str(b));}
const one=q(1),two=q(2);
for(let A=1;A<=12;A++)for(let K=1;K<=10;K++)for(let h0=1;h0<=8;h0++){
  const a0=q(A,6),k0=q(K,5),a=sq(a0),k=sq(k0),h=q(h0,3);
  const interior=le(a,div(k,sq(h)));
  const x=interior?add(k,mul(two,mul(a0,k0))):add(add(k,mul(h,a)),div(k,h));
  const free=div(sub(x,k),mul(two,k)),cap=div(one,h);
  const t=le(free,cap)?free:cap;
  const rate=sub(mul(t,sub(x,k)),mul(k,sq(t)));
  eq(rate,a,"inverted bulk/spike rate");
  const exponent=interior?sq(add(a0,k0)):add(mul(add(one,h),a),mul(k,add(one,div(one,h))));
  eq(add(a,x),exponent,"likelihood change exponent");
  const cross=div(k,sq(h));
  eq(sq(add(div(k0,h),k0)),
     add(mul(add(one,h),cross),mul(k,add(one,div(one,h)))),"two branches agree at crossover");
}
for(let d=2;d<=20;d++)for(let r=0;r<=d;r++)for(let s=1;s<d;s++){
  const u=q(r,d),h=q(s,d),noise=sub(one,u);
  eq(add(u,noise),one,"channel fixes unit variance");
  eq(add(mul(u,sub(one,h)),noise),sub(one,mul(u,h)),"channel reduces mismatch");
}
console.log("OK: "+checks+" exact rate and scalar-channel checks.");

// Illustrative finite-dimensional checks: for isotropic narrowing, under P the
// sufficient radius squared / (2 lambda) is Gamma(shape=D/2, rate=1), and under
// Q the same event uses radius squared / 2.
function logFact(n){let l=0;for(let j=2;j<=n;j++)l+=Math.log(j);return l;}
function lowerGamma(k,x,fact){
  let s=1,term=1;
  for(let j=k+1;j<k+100000;j++){
    term*=x/j;s+=term;
    if(term<s*1e-15)break;
  }
  return Math.log(s)-x+k*Math.log(x)-fact;
}
function gammaQuantile(k,logp,fact){
  let lo=0,hi=k;
  for(let i=0;i<64;i++){const v=(lo+hi)/2;
    if(lowerGamma(k,v,fact)<logp)lo=v;else hi=v;
  }
  return (lo+hi)/2;
}
for(const D of [2000,20000,200000]){
  const k=D/2,lf=logFact(k),logD=Math.log(D),a=0.75,B=1;
  const lam=1-Math.sqrt(logD/D)/(B*B);
  const x=gammaQuantile(k,-a*logD,lf);
  const logQ=lowerGamma(k,lam*x,lf);
  if(!(logQ < -a*logD) || Math.abs(lowerGamma(k,x,lf)+a*logD)>1e-7)
    throw Error("Unexpected gamma tail.");
  console.log({D,lossExponent:-logQ/logD,limitingExponent:(Math.sqrt(a)+1/(2*B*B))**2});
}
