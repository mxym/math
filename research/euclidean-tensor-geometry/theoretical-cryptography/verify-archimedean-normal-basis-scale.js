"use strict";
// Exact toy cyclotomic orbit Gram matrices, using integer Ramanujan traces.
// No lattice solver or cryptographic samples.
let checks=0;
const assert=(yes,msg)=>{if(!yes)throw Error(msg);++checks;};
const mod=(x,m)=>(x%m+m)%m;
function primitive(p,h){
  const n=p**h, phi=n-n/p;
  for(let a=2;a<n;++a){
    if(a%p===0)continue;
    let b=a, count=1;
    while(b!==1 && count<=phi){b=b*a%n;++count;}
    if(count===phi)return a;
  }
  throw Error("no primitive root found");
}
function pow(a,k,n){
  let r=1;
  for(;k>0;k=Math.floor(k/2)){
    if(k%2)r=r*a%n;
    a=a*a%n;
  }
  return r;
}
function put(v,i,c){v.set(i,(v.get(i)||0n)+c);}
function addTransform(out,v,f,coeff,N){
  for(const [i,c] of v)put(out,i*f%N,coeff*c);
}
function eta(p,h,d,N){
  const n=p**h, phi=n-n/p, a=primitive(p,h), s=pow(a,d,n);
  const v=new Map();
  for(let j=0,x=1;j<phi/d;++j,x=x*s%n)put(v,x*(N/n),1n);
  return v;
}
function tame(p,d,N){
  if(d===1)return new Map([[0,1n]]);
  const v=eta(p,1,d,N), out=new Map([[0,BigInt(2*(p-1)/d)]]);
  for(let x=2;x<p;++x)addTransform(out,v,mod(x*(1-x),p),1n,N);
  return out;
}
function wild(p,a,N){
  const out=new Map([[0,1n]]), g=primitive(p,a+1);
  for(let j=1;j<=a;++j){
    const v=eta(p,j+1,p**j,N);
    if(j%2)addTransform(out,v,1,BigInt(p)**BigInt((j-1)/2),N);
    else for(let u=1;u<p;++u){
      const ls=pow(u,(p-1)/2,p)===1?1n:-1n;
      addTransform(out,v,pow(g,u*(p**(j-1)),N),ls*BigInt(p)**BigInt((j-2)/2),N);
    }
  }
  return out;
}
function mult(A,B,N){
  const out=new Map();
  for(const [x,a] of A)for(const [y,b] of B)put(out,(x+y)%N,a*b);
  return new Map([...out].filter(([,c])=>c!==0n));
}
function traceTerms(v,w,p,N){
  const m=N/p;
  const ram=x=>(x%N===0?BigInt(N):0n)-(x%m===0?BigInt(m):0n);
  let s=0n;
  for(const [x,a] of v)for(const [y,b] of w)s+=a*b*ram(x+y);
  return s;
}
function gram(p,a,d,t,V){
  const N=p**(a+1), n=p**a*d, H=BigInt((N-N/p)/n), s=primitive(p,a+1);
  const trace=traceTerms(V,[[0,1n]],p,N);
  assert(trace===H*BigInt(t),"orbit trace");
  for(let j=0,u=1;j<n;++j,u=u*s%N){
    const R=new Map();addTransform(R,V,u,1n,N);
    const S=traceTerms(V,R,p,N);
    assert(S===(j===0?H*BigInt(t)**2n:0n),"orthogonal orbit Gram");
  }
}
for(const p of [7,11,13,19,31,37,43,61,71]){
  for(let d=3;d<p;d+=2)
    if((p-1)%d===0)gram(p,0,d,p,tame(p,d,p));
}
for(const p of [3,5,7,11])
for(let a=1;a<=(p<8?3:2);++a){
  const N=p**(a+1);
  gram(p,a,1,p**a,wild(p,a,N));
  if(a<=2)for(let d=3;d<p;d+=2){
    if((p-1)%d!==0)continue;
    const W=mult(tame(p,d,N),wild(p,a,N),N);
    gram(p,a,d,p**(a+1),W);
  }
}
for(const p of [3,5,7,11,13,17,19,23,29,31,41,47,101])
for(let a=1;a<=8;++a)
for(let d=1;d<p;d+=2){
  if((p-1)%d!==0)continue;
  const P=BigInt(p), T=BigInt(d), A=BigInt(a);
  const pa=P**A, e=T*pa, sum=(pa-1n)/(P-1n);
  let disc=T-1n;
  for(let j=1n;j<=A;++j)disc+=T*(P**j-P**(j-1n))*(j+1n);
  assert(disc===e*(A+1n)-T*sum-1n,"conductor-discriminant sum");
  const rel=disc-(T-1n)*pa;
  assert(rel/pa===T*A,"relative trace ideal exponent");
  assert((rel+pa-1n)/pa===T*A+1n,"strict different remainder");
}
for(let x=0;x<3;++x)for(let y=0;y<3;++y)
  if((x*x+y*y)%3===0)assert(x===0&&y===0,"Gaussian norm obstruction at 3");
assert(4*4%13===3&&5*5%13===12,"split modular toy fiber");
console.log("Archimedean normal basis: "+checks+" exact checks passed.");
