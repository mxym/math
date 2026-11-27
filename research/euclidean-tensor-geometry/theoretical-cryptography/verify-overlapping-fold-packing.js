'use strict';
// All experiments are tiny additive probability tables; no cryptographic samples or solvers.
const q=3, weights=[2n,1n,1n];
const mod=x=>(x%q+q)%q;
function table(cols) {
 let d=[1n,...Array(8).fill(0n)];
 for(const [a,b] of cols) {
  const n=Array(9).fill(0n);
  for(let x=0;x<3;x++)for(let y=0;y<3;y++)for(let e=0;e<3;e++)n[3*mod(x+a*e)+mod(y+b*e)]+=d[3*x+y]*weights[e];
  d=n;
 }
 return d;
}
const sum=a=>a.reduce((s,x)=>s+x,0n);
const abs=x=>x<0n?-x:x;
function chiPlus(d) {return [BigInt(d.length)*sum(d.map(x=>x*x)),sum(d)**2n];}
function tv(d){const n=BigInt(d.length),s=sum(d);return [sum(d.map(x=>abs(n*x-s))),2n*n*s];}
let checks=0;
function cmp(A,B,kind){checks++;let d=A[0]*B[1]-A[1]*B[0];if(kind==='eq'?d!==0n:kind==='gt'?d<=0n:kind==='ge'?d<0n:d>0n)throw Error([A,B,kind].join(' '));}
const u=[1,1],v=[1,-1],rep=(c,n)=>Array.from({length:n},()=>c);
const fac=n=>16n**BigInt(n);
for(let r=1;r<=4;r++)for(let t=1;t<=4;t++){
 let d=table([...rep(u,r),...rep(v,t)]);
 cmp(chiPlus(d),[(fac(r)+2n)*(fac(t)+2n),fac(r)*fac(t)],'eq');
 // The best fractional packing here is min(r,t): each invertible block needs one of each type.
 let k=Math.min(r,t);
 cmp(chiPlus(d),[(fac(k)+2n)**2n,fac(k)**2n],r===t?'eq':'le');
 if(t===1)cmp(tv(d),tv(weights),'ge');
}
// Three overlapping bases, each of weight 1/2: kappa=3/2; nontrivial scalar transform =1/4.
const fr=table([[1,0],[0,1],[1,1]]);
cmp(chiPlus(fr),[66n**2n,64n**2n],'le');
// Rank-deficient: identical rows always collide on the diagonal in the output.
const singular=table(rep(u,3));
cmp(tv(singular),[2n,3n],'ge');
// Rectangular surjectivity, no invertible singleton, Z/15. Uniform noise is exactly uniform at output.
const rect=Array(15).fill(0);
for(let x=0;x<15;x++)for(let y=0;y<15;y++)rect[(3*x+5*y)%15]++;
if(!rect.every(v=>v===15))throw Error('rectangular block');checks++;
console.log({checks,fractionalBound:'(66/64)^2 for 1+chi^2',fractionalActual:chiPlus(fr).map(String)});
