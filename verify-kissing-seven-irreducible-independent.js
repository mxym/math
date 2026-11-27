'use strict';
// Independent exact interval replay of the single-seed H=C_2^3:C_7 bound.
// Requires only Node.js. No precomputed bins, dependencies, or input files.
// Pruning bounds are outward extensions of each closed continuous box.
const assert=require('node:assert/strict');
const S=16384,N=S*S,R=7*1024,F=2**18,T=256;
assert.equal(N%F,0); assert.equal(F%T,0);
const chars=[1,2,4,3,6,7,5]; // consecutive powers of x modulo x^3+x+1
const idx=[0,1,2,3,4,5,6];
const sgn=(i,m)=>[1,-1,-1,1,-1,1,1,-1][chars[i]&m];
const uSign=i=>i===0?-1:1;
const w=Array.from({length:8},(_,m)=>idx.map(i=>sgn(i,m)*uSign(i)));
const flips=Array.from({length:7},(_,m)=>idx.filter(i=>sgn(i,m+1)===-1));
const forwards=Array.from({length:32},(_,g)=>({k:g>>3,m:g%8})).slice(1).map(({k,m})=>{
 const pair=idx.map(i=>{const j=(i+k)%7;return [i,j,sgn(i,m)*uSign(i)*uSign(j)]});
 return {k,pair,mult:k===0?1:2};
});
assert.equal(forwards.reduce((a,g)=>a+g.mult,0),55);
const fl=Math.floor,cl=Math.ceil;
function rt(n){
 assert(n>=0&&Number.isSafeInteger(n));
 let x=fl(Math.sqrt(n));
 if((x+1)*(x+1)<=n)x++;
 if(x*x>n)x--;
 assert(x*x<=n&&n<(x+1)*(x+1));
 return x;
}
function up(n){const x=rt(n);return x*x===n?x:x+1}
const B=up(7*N/4),base=8*R*R;
const lo1=fl(127*F/200),hi1=cl(127*F/200),lo2=fl(F/10),hi2=cl(F/10);
const prod=n=>fl(n/F);
assert(7*5405*T*R*R+1112*base*T<2**53);
assert(7*base*55*132*T<2**53);
// The interval is closed also at t=-1 and t=1/2. Crossings of
// -127/200 or -1/10 give zero without interpolating polynomial values.
function minusF(a,b){
 const l=fl(Math.max(-N,a)/(N/F)),h=cl(Math.min(N/2,b)/(N/F));
 if(l>h)return 0;
 let X=F/2-h,Y=l+13*F/4,D=Math.max(0,l+lo1,-h-hi1),E=Math.max(0,l+lo2,-h-hi2);
 let z=prod(22*X*Y); z=prod(z*D); z=prod(z*D); z=prod(z*E);return prod(z*E);
}
function lin(row,a,b){
 let l=0,u=0;for(let i=0;i<7;i++){if(row[i]>0){l+=a[i];u+=b[i]}else{l-=b[i];u-=a[i]}}return [l,u];
}
// Upper bound on sum (R q_s)^2 by the continuous box LP with sum=8R/7.
// By convex secants, using this upper bound can only retain extra boxes.
function fourth(a,b){
 let d=8*R/7,v=0;const c=[];
 for(const row of w){
  const [l,u]=lin(row,a,b),lo=fl((R*Math.max(0,l,-u)**2)/(7*N)),hi=Math.min(R/4,cl(R*Math.max(l*l,u*u)/(7*N)));
  if(lo>hi)return -1;
  c.push({s:lo+hi,h:hi-lo});d-=lo;v+=lo*lo;
 }
 if(d<0)return -1;
 c.sort((x,y)=>y.s-x.s);
 for(const {s,h} of c){const delta=Math.min(d,h);v+=s*delta;d-=delta}
 return d?-1:v;
}
let visits,depthMax,cut;
function visit(a,b,p,d){
 visits++;if(d>depthMax)depthMax=d;
 for(let round=0;round<2;round++){
  const a2=a.map(x=>x*x),b2=b.map(x=>x*x),sum=(x,y)=>x+y,A=a2.reduce(sum),C=b2.reduce(sum);
  if(A>N||C<N)return;
  a[p]=Math.max(...a);
  for(let i=0;i<7;i++){
   a[i]=Math.max(a[i],rt(Math.max(0,N-C+b2[i])));
   b[i]=Math.min(b[i],b[p],up(N-A+a2[i]));if(a[i]>b[i])return;
  }
  for(const I of flips){
   let z=0;for(const i of I)z+=b[i]*b[i];if(z<N/4)return;
   for(const i of I)a[i]=Math.max(a[i],rt(Math.max(0,N/4-z+b[i]*b[i])));
  }
  for(const row of w){
   const [l,u]=lin(row,a,b);if(l>B||u< -B)return;
   for(let i=0;i<7;i++){
    const x=a[i],y=b[i];
    if(row[i]>0){a[i]=Math.max(x,y-B-u);b[i]=Math.min(y,x+B-l)}
    else{a[i]=Math.max(x,y+l-B);b[i]=Math.min(y,x+u+B)}
    if(a[i]>b[i])return;
   }
  }
 }
 const M=fourth(a,b);if(M<0)return;
 const need=T*(7*5405*M-1112*base);
 let z=0;
 if(need<0){cut++;return}
 for(const {k,pair,mult} of forwards){
  let l=0,u=0;
  if(k===0){
   let aN=0,bN=0,aP=0,bP=0;
   for(const [i,,sign] of pair){if(sign===1){aP+=a[i]*a[i];bP+=b[i]*b[i]}else{aN+=a[i]*a[i];bN+=b[i]*b[i]}}
   l=Math.max(N-2*bN,2*aP-N);u=Math.min(N-2*aN,2*bP-N);
  }else for(const [i,j,sign] of pair){
    if(sign===1){l+=a[i]*a[j];u+=b[i]*b[j]}else{l-=b[i]*b[j];u-=a[i]*a[j]}
  }
  if(l>N/2||u< -N||l>u)return;
  z+=mult*minusF(l,u);
  if(fl(z/(F/T))*7*base>need){cut++;return}
 }
 let i=-1,h=1;
 // Closed bisection, widest nonpivot interval, in reverse order.
 for(let j=6;j>=0;j--)if(j!==p&&b[j]-a[j]>h){h=b[j]-a[j];i=j}
 assert(i>=0&&d<80,'unresolved continuous box');
 const m=fl((a[i]+b[i])/2),c=b.slice(),e=a.slice();c[i]=m;e[i]=m;
 visit(a.slice(),c,p,d+1);visit(e,b,p,d+1);
}
for(const p of [0,1,3]){
 const a=idx.map(i=>i===p?rt(fl(N/7)):0),b=idx.map(()=>up(5*N/8));
 visits=depthMax=cut=0;visit(a,b,p,0);
 console.log('pivot',p,'nodes',visits,'depth',depthMax,'positive-bound boxes',cut);
}
