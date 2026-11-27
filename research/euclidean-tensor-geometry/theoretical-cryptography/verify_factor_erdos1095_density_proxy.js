"use strict";

// Exact small-fixture checks and a rational bracket for the logarithmic constant.
// Run: node verify_factor_erdos1095_density_proxy.js
let assertions=0, localResidues=0, globalResidues=0;
const eq=(b,label)=>{++assertions;if(!b) throw Error(label);};
const div=(n,p)=>Math.floor(n/p);
function primesTo(n) {
  const out=[];
  for(let p=2;p<=n;++p) if(!out.some(q=>q*q<=p&&p%q===0))out.push(p);
  return out;
}
function digits(k,p) {
  const a=[];
  do { a.push(k%p);k=div(k,p); } while(k);
  return a;
}
function permitted(n,a,p) {
  for(const d of a) {
    if(n%p<d)return false;
    n=div(n,p);
  }
  return true;
}
function legendre(n,p) {
  let v=0;
  while(n>=p) {n=div(n,p);v+=n;}
  return v;
}
const ps=primesTo(120);
for(let k=2;k<=120;++k) {
  const local=[];
  for(const p of ps) {
    if(p>k)break;
    const a=digits(k,p), m=p**a.length;
    const t=a.findIndex(d=>d>0), d=(p**t)*(p-a[t]);
    const r=p-a[0];
    eq((k+r)%p===0&&1<=r&&r<=p,"low-digit gap");
    eq((d===1)===((k+1)%p===0),"local exact zero criterion");
    const bits=new Uint8Array(m);
    for(let n=0;n<m;++n) bits[n]=+permitted(n,a,p);
    let R=0,J=0;
    for(let n=0;n<m;++n){R+=bits[n];J+=bits[n]*bits[(n+1)%m];}
    eq(R===a.reduce((u,b)=>u*(p-b),1),"local single count");
    eq(J*d===R*(d-1),"local adjacent count");
    for(let n=k;n<=k+100;++n) {
      const valuation=legendre(n,p)-legendre(k,p)-legendre(n-k,p);
      eq((valuation===0)===!!bits[n%m],"independent Legendre check");
    }
    local.push({m,bits,R,J});
    localResidues+=m;
  }
  const primeK1=primesTo(k+1).includes(k+1);
  eq(local.every(x=>x.J>0)===primeK1,"global zero criterion");
  if(k<=10) {
    const M=local.reduce((P,x)=>P*x.m,1);
    const u=local.reduce((P,x)=>P*x.R,1);
    const v=local.reduce((P,x)=>P*x.J,1);
    let r=0,j=0;
    for(let n=0;n<M;++n) {
      if(local.every(x=>x.bits[n%x.m])) {
        ++r;
        if(local.every(x=>x.bits[(n+1)%x.m]))++j;
      }
    }
    eq(r===u&&j===v,"CRT full-period count");
    globalResidues+=M;
  }
}
// Atanh series for log(1+1/a), with z=1/(2a+1).
// Floor each scaled term. After the first term below one unit, the
// unsummed contribution is < 1/(1-z^2) <= 9/8 units.
const S=10n**30n, N=500000;
let lo=0n,hi=0n;
for(let a=1;a<=N;++a) {
  const b=BigInt(a+1),z=BigInt(2*a+1),z2=z*z;
  let pow=z,sum=0n, count=0n;
  for(let j=1n;;j+=2n) {
    const F=2n*S/(j*pow*b);
    if(F===0n)break;
    sum+=F;++count;pow*=z2;
  }
  lo+=sum;
  hi+=sum+count+2n;
}
// log(1+1/a) lies between 1/(a+1) and 1/a;
// integral comparison and telescoping bound the tail by 1/(N+2), 1/(N+1).
lo+=S/BigInt(N+2);
hi+=(S+BigInt(N))/BigInt(N+1);
eq(78853056590n*(S/10n**11n)<lo && hi<78853056592n*(S/10n**11n),"certified C0 decimal");
const fmt=x=>(x/S)+"."+(x%S).toString().padStart(30,"0");
console.log("PASS: "+assertions+" exact assertions, "+localResidues+
            " local and "+globalResidues+" full-period residues, k<=120");
console.log("C0 is between "+fmt(lo)+" and "+fmt(hi));
