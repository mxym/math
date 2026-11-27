'use strict';
// Fixed toy verification of rational moment identities and Gaussian comparisons.
let exact=0,numeric=0;
function check(ok,label){if(!ok)throw Error(label);exact++;}
function near(x,y,e,label){if(!Number.isFinite(x)||!Number.isFinite(y)||Math.abs(x-y)>e)throw Error(label+': '+x+' vs '+y);numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;return b?gcd(b,a%b):a;}
function rat(a,b=1n){a=BigInt(a);b=BigInt(b);if(b<0n){a=-a;b=-b;}const g=gcd(a,b);return [a/g,b/g];}
const add=(a,b)=>rat(a[0]*b[1]+a[1]*b[0],a[1]*b[1]);
const neg=a=>[-a[0],a[1]], sub=(a,b)=>add(a,neg(b));
const mul=(a,b)=>rat(a[0]*b[0],a[1]*b[1]);
const div=(a,b)=>rat(a[0]*b[1],a[1]*b[0]);
const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
const Z=rat(0),U=rat(1);
const rf=(x)=>Number(x[0])/Number(x[1]);
const ssum=xs=>xs.reduce(add,Z);
const fs=[1n];for(let i=1;i<=100;i++)fs.push(fs[i-1]*BigInt(i));
const choose=(n,k)=>fs[n]/fs[k]/fs[n-k];
const bMom=k=> k&1 ? Z : rat(2,(k+1)*(k+2));
function gMom(k,v){if(k&1)return Z;return rat(fs[k]*BigInt(v)**BigInt(k/2),2n**BigInt(k/2)*fs[k/2]);}
const inv=[U];
for(let j=1;j<=72;j++){
  const x=neg(ssum(seq(j).map(i=>mul(inv[i],div(bMom(j-i),rat(fs[j-i]))))));
  inv.push(x);
  if(j&1)check(x[0]===0n,'reciprocal odd coefficient');
  else check((x[0]>0n)===(j%4===0),'reciprocal even sign');
}
function vMom(k,v){
 return ssum(seq(k+1).map(j=>mul(inv[j],mul(gMom(k-j,v),rat(fs[k]/fs[k-j])))));
}
function kMom(k,raw){
 return ssum(seq(k+1).map(j=>mul(rat(choose(k,j)),mul(bMom(j),raw[k-j]))));
}
function pos(M,label){
 const a=M.map(x=>x.slice());
 for(let k=0;k<a.length;k++){
   check(a[k][k][0]>0n,label);
   for(let i=k+1;i<a.length;i++)for(let j=k+1;j<a.length;j++)
      a[i][j]=sub(a[i][j],div(mul(a[i][k],a[k][j]),a[k][k]));
 }
}
function lin(A,y){
 const a=A.map((row,i)=>row.concat([y[i]])),n=A.length;
 for(let k=0;k<n;k++){
   check(a[k][k][0]!==0n,'exact elimination pivot');
   let d=a[k][k];for(let j=k;j<=n;j++)a[k][j]=div(a[k][j],d);
   for(let i=0;i<n;i++)if(i!==k){
     const q=a[i][k];
     for(let j=k;j<=n;j++)a[i][j]=sub(a[i][j],mul(q,a[k][j]));
   }
 }
 return a.map(row=>row[n]);
}
for(let r=1;r<=12;r++){
 const v=r+1,n=r+1,raw=seq(2*r+3).map(k=>vMom(k,v));
 for(let k=0;k<=2*r+2;k++)check(eq(kMom(k,raw),gMom(k,v)),'formal inverse times base gives exact Gaussian moments');
 const H=seq(n+1).map(i=>seq(n+1).map(j=>raw[i+j]));
 const HG=seq(n+1).map(i=>seq(n+1).map(j=>gMom(i+j,v)));
 pos(H.map((row,i)=>row.map((a,j)=>sub(a,mul(rat(1,2),HG[i][j])))),'lower Gaussian Gram comparison');
 pos(H.map((row,i)=>row.map((a,j)=>sub(mul(rat(3,2),HG[i][j]),a))),'upper Gaussian Gram comparison');
 const A=H.slice(0,n).map(row=>row.slice(0,n)),C=seq(n).map(i=>seq(n).map(j=>raw[i+j+1]));
 const columns=seq(n).map(j=>lin(A,C.map(row=>row[j])));
 const J=seq(n).map(i=>columns.map(col=>col[i]));
 let a=seq(n).map(i=>i===0?U:Z);
 for(let k=0;k<=2*r+1;k++){
   check(eq(ssum(A[0].map((x,i)=>mul(x,a[i]))),raw[k]),'exact compressed multiplication moment');
   a=J.map(row=>ssum(row.map((x,i)=>mul(x,a[i]))));
 }
 for(const sign of [-1,1])pos(A.map((row,i)=>row.map((x,j)=>add(mul(rat(4*(r+1)-1),x),mul(rat(sign),C[i][j])))),'spectral support fits claimed radius');
}

// A generic finite symmetric mixture of shifted triangles satisfies both identities.
for(let x=-1000;x<=1000;x++){
 const d=100,w=[1,3,1],a=[-70,0,70];
 let mass=0,first=0;
 for(let k=-15;k<=15;k++)for(let j=0;j<3;j++){
   const p=Math.max(0,d-Math.abs(x-k*d-a[j]))*w[j];
   mass+=p;first+=p*(x-k*d);
 }
 check(mass===5*d,'exact mass partition');
 check(first===0,'exact affine reproduction');
}

const pdf=x=>Math.exp(-x*x/2)/Math.sqrt(2*Math.PI);
const gauss=(x,s)=>pdf(x/s)/s;
function He(n,x){let p=1,q=x;if(n===0)return p;for(let j=1;j<n;j++){const t=x*q-j*p;p=q;q=t;}return q;}
function simpson(f,a,b,N){
 let h=(b-a)/N,out=f(a)+f(b);
 for(let k=1;k<N;k++)out+=(k&1?4:2)*f(a+k*h);
 return out*h/3;
}
function tri(x,s){return simpson(y=>(1+y)*gauss(x+y,s),-1,0,256)+simpson(y=>(1-y)*gauss(x+y,s),0,1,256);}
for(const r of [1,2]){
 const v=r+1,raw=seq(2*r+4).map(k=>vMom(k,v)),m2=rf(raw[2]),m4=rf(raw[4]);
 const a2=r===1?m2:m4/m2,p=m2/a2,a=Math.sqrt(a2);
 const qa=seq(2*r+4).map(k=>k===0?1:k&1?0:p*Math.pow(a,k));
 for(let k=0;k<=2*r+1;k++)near(qa[k],rf(raw[k]),1e-9,'explicit low-order quadrature atoms');
 const q=2*r+2;
 let moment=0;
 for(let j=0;j<=q;j++)moment+=Number(choose(q,j))*rf(bMom(j))*qa[q-j];
 const delta=moment-rf(gMom(q,v));
 const coeff=Math.abs(delta)/(2*Number(fs[q]))*simpson(x=>Math.abs(He(q,x))*pdf(x),-10,10,14000);
 for(const c of [0,.31,.53]){
   for(const s of [14,24,32]){
     const bound=Math.ceil(10*s+10);let mass=0,Z=0,tv=0;
     for(let k=-bound;k<=bound;k++)Z+=gauss(k-c,Math.sqrt(s*s+v));
     for(let k=-bound;k<=bound;k++){
       const x=k-c,law=(1-p)*tri(x,s)+(p/2)*(tri(x+a,s)+tri(x-a,s));
       mass+=law;tv+=Math.abs(law-gauss(x,Math.sqrt(s*s+v))/Z)/2;
     }
     near(mass,1,5e-13,'rounded Gaussian normalization');
     near(tv*Math.pow(s,q)/coeff,1,r===1?.035:.085,'first mismatching moment TV coefficient');
   }
 }
}
console.log({exact_checks:exact,numerical_checks:numeric});
