"use strict";
// Exact finite checks for the smooth/rough block decomposition, the cutoff
// counting bound, the cone gadget, and the two-weight atom family.
const assert=require("node:assert/strict");
let checks=0;
const ok=x=>{++checks;assert.ok(x);};
const eq=(x,y)=>{++checks;assert.equal(x,y);};
const prime=p=>p>=2&&Array.from({length:Math.floor(Math.sqrt(p))-1},(_,i)=>i+2).every(d=>p%d);
const gcd=(a,b)=>b?gcd(b,a%b):a;
function smooth(n,primes) {
 for(const p of primes)while(n%p===0)n/=p;
 return n===1;
}
function freeOf(n,primes) {return primes.every(p=>n%p!==0);}
function signature(n,d) {
 const v=[];
 for(let j=2;j<=n;++j)if(n%j===0&&d%j!==0)v.push(j);
 return v;
}
// Direct enumeration retaining all distinct vectors of cyclotomic exponents.
function enumerate(D,primes,kind) {
 const ns=2*D+1, generators=[];
 for(const p of primes)for(let i=1;(p-1)*i<=D;++i)
   if(kind!=="local"||smooth(i,primes))generators.push([(p-1)*i,signature(p*i,i)]);
 if(kind==="augmented")for(let i=2;i<=D+1;++i)generators.push([i-1,signature(i,1)]);
 const rows=Array.from({length:D+1},()=>new Set());
 const zero=Array(ns).fill(0);
 rows[0].add(String.fromCharCode(...zero));
 for(let d=0;d<D;++d)for(const k of rows[d]) {
  const a=Array.from(k,c=>c.charCodeAt(0));
  for(const [w,idx] of generators)if(d+w<=D) {
   for(const j of idx)++a[j];
   rows[d+w].add(String.fromCharCode(...a));
   for(const j of idx)--a[j];
  }
 }
 return rows.map(x=>BigInt(x.size));
}
function product(a,b) {
 const D=a.length-1,z=Array(D+1).fill(0n);
 for(let i=0;i<=D;++i)if(a[i])for(let j=0;i+j<=D;++j)if(b[j])z[i+j]+=a[i]*b[j];
 return z;
}
function partitions(D) {
 const z=Array(D+1).fill(0n);z[0]=1n;
 for(let k=1;k<=D;++k)for(let j=k;j<=D;++j)z[j]+=z[j-k];
 return z;
}
function block(D,primes) {
 const local=enumerate(D,primes,"local");
 let z=Array(D+1).fill(0n);z[0]=1n;
 for(let m=1;m<=D;++m)if(freeOf(m,primes)) {
  const f=Array(D+1).fill(0n);
  for(let d=0;d*m<=D;++d)f[d*m]=local[d];
  z=product(z,f);
 }
 for(let m=2;m<=D+1;++m)if(freeOf(m,primes))
  for(let d=m-1;d<=D;++d)z[d]+=z[d-(m-1)];
 return z;
}
const D=21, all=Array.from({length:D+2},(_,i)=>i).filter(prime);
const hs=enumerate(D,all,"ordinary"), part=partitions(D);
const snapshots={};
for(const Y of [1,2,3,5,7]) {
 const S=all.filter(p=>p<=Y), e=enumerate(D,S,"augmented");
 const z=block(D+Math.floor(D/Y),S);
 for(let n=0;n<=D;++n) {
  eq(e[n],z[n]);
  ok(z[n]<=hs[n]);
  let r=0n;for(let d=0;d<=Math.floor(n/Y);++d)r+=z[n+d]*part[d];
  ok(hs[n]<=r);
 }
 snapshots[Y]=e.slice(0,13).map(Number);
}
const T=80, actual=Array(T+1).fill(0n), cone=Array(T+1).fill(0n);
for(let a=0;a<=T;++a)for(let b=0;a+2*b<=T;++b)
 for(let c=0;c<=a+b&&a+2*b+2*c<=T;++c)++actual[a+2*b+2*c];
cone[0]=1n;
for(const w of [1,2,3,4])for(let j=w;j<=T;++j)cone[j]+=cone[j-w];
for(let d=0;d<=T;++d)eq(actual[d],cone[d]-(d>=5?cone[d-5]:0n));

// Reconstruct the enlarged independent block count in smooth supports.
const [L,U]=[2,3];
for(const primes of [[2,3],[2,3,5],[2,3,5,7]]) {
 const z=Array(D+1).fill(0n);z[0]=1n;
 for(let n=2;n<=2*D;++n)if(smooth(n,primes)) {
  let m=n;while(m%L===0)m/=L;while(m%U===0)m/=U;
  if([2,3,6].includes(n/m))continue;
  const p=primes.find(p=>n%p===0), w=n-n/p;
  for(let i=w;i<=D;++i)z[i]+=z[i-w];
 }
 let f=z;
 for(let m=1;m<=D;++m)if(smooth(m,primes.slice(2))) {
  const r=Array(D+1).fill(0n);
  for(let i=0;i*m<=D;++i)r[i*m]=actual[i];
  f=product(f,r);
 }
 const direct=enumerate(D,primes,"local");
 for(let i=0;i<=D;++i)ok(f[i]<=direct[i]);
}

let atoms=0;
for(let a=2;a<=23;++a)for(let b=a+1;b<=29;++b)if(gcd(a,b)===1){
 const d=a*b, P=Array(d+1).fill(0n);P[0]=1n;
 for(const x of [a+b,a*b])for(let n=d;n>=x;--n)P[n]-=P[n-x];
 for(const x of [a,b])for(let n=x;n<=d;++n)P[n]+=P[n-x];
 for(let n=0;n<=d;++n)eq(P[n],n%a===0||n%b===0?1n:0n);
 for(let i=1;i<b;++i)for(let j=1;j<a;++j) {
  const m=i*a+j*b;
  if(m<=d)eq(P[m],0n);
 }
 ++atoms;
}
// Test the stronger top-index result on all cyclotomic products of
// degree <=16 that pass the sorted Gale condition, regardless of signs.
const DG=16, N=2*DG*DG;
const mu=n=>{
 let g=1;
 for(let p=2;p*p<=n;++p)if(n%p===0){
  n/=p;g=-g;if(n%p===0)return 0;
 }
 return n>1?-g:g;
};
const phi=n=>{let t=0;for(let i=1;i<=n;++i)if(gcd(n,i)===1)++t;return t;};
const candidates=[];
for(let n=2;n<=N;++n){
 const w=phi(n);if(w>DG)continue;
 const ds=[];for(let b=1;b<=n;++b)if(n%b===0&&mu(n/b))ds.push([b,mu(n/b)]);
 const p=Array.from({length:n-1},(_,i)=>i+2).find(d=>n%d===0);
 candidates.push({n,w,ds,least:n-n/p,d:n/p});
}
const ex=Array(N+1).fill(0), active=[];
let galeChecked=0;
function testGale(k,deg) {
 let balance=0;
 // Every admissible factor index is <=N since phi(n)^2>=n/2.
 for(let i=N;i>=1;--i){balance+=ex[i];if(balance<0)break;}
 if(balance>=0) {
  ++galeChecked;
  for(const f of active) {
   ok(deg>=f.least);
   if(deg===f.least) {
    for(let i=1;i<=N;++i)eq(ex[i],(i===f.n?1:0)-(i===f.d?1:0));
   }
  }
 }
 for(let i=k;i<candidates.length;++i){
  const f=candidates[i];if(deg+f.w>DG)continue;
  active.push(f);for(const [j,v] of f.ds)ex[j]+=v;
  testGale(i,deg+f.w);
  active.pop();for(const [j,v] of f.ds)ex[j]-=v;
 }
}
testGale(0,0);
console.log("Monomial HSOP checks passed: "+checks+" (degree cutoffs, cone series and "+atoms+" atom controls, "+galeChecked+" Gale lists)");
console.log(JSON.stringify({snapshots,monomial:hs.slice(0,13).map(Number)}));
