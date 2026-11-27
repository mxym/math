'use strict';
/* Exact arithmetic for generated probability tables and support masks.
 * This does not process observations or run a cryptographic procedure. */
const assert=require('node:assert/strict');
const seq=n=>Array.from({length:n},(_,i)=>i);
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a;}
function rat(n,d=1n){const g=gcd(n,d);return [n/g,d/g];}
const qa=(n,d=1)=>rat(BigInt(n),BigInt(d)),add=(a,b)=>rat(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const neg=a=>[-a[0],a[1]],sub=(a,b)=>add(a,neg(b)),mul=(a,b)=>rat(a[0]*b[0],a[1]*b[1]);
const sum=a=>a.reduce(add,qa(0)),prod=a=>a.reduce(mul,qa(1)),div=(a,b)=>rat(a[0]*b[1],a[1]*b[0]);
const absq=a=>[abs(a[0]),a[1]];
let exact=0;
function ck(a,b){assert.deepEqual(a,b);exact++;}
function tr(b){assert(b);exact++;}
function maps(ns){return ns.reduce((w,n)=>w.flatMap(a=>seq(n).map(j=>[...a,j])),[[]]);}
function ptable(q,m){
  const raw=seq(m).map(i=>rat(BigInt(q-1),BigInt(q)**BigInt(i+1)));
  const total=sub(qa(1),rat(1n,BigInt(q)**BigInt(m)));
  const a=raw.map(t=>div(t,total));ck(sum(a),qa(1));ck(sum(raw),total);
  const cnt=Array(m).fill(0);
  for(const v of maps(Array(m).fill(q))){
    const i=v.findIndex(x=>x!==0);if(i>=0)cnt[i]++;
  }
  ck(cnt.map(x=>qa(x,q**m-1)),a);
  return a;
}
function masks(labels,m){
  const b=Array(m).fill(0);for(let j=0;j<labels.length;j++)b[labels[j]]|=1<<j;
  return b.filter(x=>x!==0);
}
const norm=n=>seq(1<<n).map(()=>qa(1,1<<n));
function margs(dist,block){
  const d=dist.map(()=>qa(0));
  for(let x=0;x<dist.length;x++)d[x&block]=add(d[x&block],dist[x]);
  return d;
}
function rec(dist,g,part){
  const a=part.map(B=>[B,margs(dist,B)]);
  return seq(1<<g).map(x=>prod(a.map(([B,p])=>p[x&B])));
}
function valFourier(d,M){
  const parity=x=>{let s=0;while(x){s^=1;x&=x-1;}return s;};
  return sum(d.map((q,x)=>parity(x&M)?neg(q):q));
}
function tv(a,b){return mul(qa(1,2),sum(a.map((p,j)=>absq(sub(p,b[j])))));}
for(const [qs,m] of [[[2,2],2],[[2,3,5],3],[[2,2,3,4],4],[[2,3,4,5],2]]){
  const g=qs.length,dim=1<<g,ps=qs.map(q=>ptable(q,m)),Z=norm(g);
  const configurations=maps(qs.map(()=>m)).map(t=>({B:masks(t,m),p:prod(t.map((i,j)=>ps[j][i])),t}));
  ck(sum(configurations.map(x=>x.p)),qa(1));
  const recomb=d=>{
    const blocks=configurations.map(({B,p})=>({x:rec(d,g,B),p}));
    return seq(dim).map(j=>sum(blocks.map(({x,p})=>mul(p,x[j]))));
  };
  const cf=[];
  for(let S=1;S<dim;S++){
    const axes=seq(g).filter(j=>S>>j&1),a=prod(axes.map(j=>qa(1,qs[j])));
    const c=mul(prod(axes.map(j=>ps[j][0])),div(sub(qa(1),prod(seq(m).map(()=>a))),sub(qa(1),a)));
    const explicit=sum(configurations.filter(({B})=>B.some(b=>(b&S)===S)).map(x=>x.p));
    ck(c,explicit);cf[S]=c;
    const X=Z.map((p,x)=>mul(p,add(qa(1),mul(qa(1,3),valFourier(seq(dim).map(j=>qa(Number(x===j))),S)))));
    const Y=recomb(X);
    ck(Y,Z.map((p,j)=>add(p,mul(c,sub(X[j],p)))));
    ck(tv(Y,X),mul(sub(qa(1),c),tv(X,Z)));
  }
  const w=seq(dim).map(j=>qa(j*j+1)),X=w.map(x=>div(x,sum(w))),Y=recomb(X);
  for(let M=1;M<dim;M++)ck(valFourier(Y,M),
    sum(configurations.map(({B,p})=>mul(p,prod(B.map(b=>valFourier(X,M&b)))))));
  const diagonal=seq(dim).map(j=>qa(Number(j===0||j===dim-1),2)),out=recomb(diagonal);
  ck(tv(diagonal,out),sub(qa(1),sum(configurations.map(({B,p})=>mul(p,qa(1,2**(B.length-1)))))));
  // The first-order effect of a common full-support shell.
  const lead=seq(dim).map(()=>qa(0));let coeff=qa(0);
  for(const {B,p} of configurations){
    if(B.length<2)continue;
    lead[0]=sub(lead[0],mul(p,qa(B.length-1)));
    lead[dim-1]=sub(lead[dim-1],p);
    for(const b of B)lead[b]=add(lead[b],p);
    coeff=add(coeff,mul(qa(B.length),p));
  }
  tr(coeff[0]>0n);ck(mul(qa(1,2),sum(lead.map(absq))),coeff);
  for(const den of [16,32,64]){
    const a=qa(1,den),expected=seq(dim).map(j=>j===0?sub(qa(1),a):j===dim-1?a:qa(0));
    const Y=recomb(expected);
    for(let j=0;j<dim;j++){
      const d=absq(sub(sub(Y[j],expected[j]),mul(a,lead[j]))),bound=qa(2**g,den*den);
      tr(d[0]*bound[1]<=bound[0]*d[1]);
    }
  }
}
function modpow(a,n,p){let x=1;for(let j=0;j<n;j++)x=x*a%p;return x;}
for(const [n,q] of [[2,5],[4,17]]){
  const points=seq(q).filter(x=>(modpow(x,n,q)+1)%q===0);ck(points.length,n);
  for(let j=0;j<n;j++)for(const p of points)tr(modpow(p,j,q)!==0);
  // Traces of signed roots in the negacyclic power basis.
  const mulroot=(x,y)=>seq(n).map(k=>k===((x+y)%n+n)%n?(Math.floor((x+y)/n)%2?-1:1):0);
  for(let j=0;j<n;j++)for(let k=0;k<n;k++)ck(n*mulroot(j,-k)[0],j===k?n:0);
}
console.log('PASS: '+exact+' exact synthetic probability, Fourier and shell checks');
