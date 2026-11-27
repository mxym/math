'use strict';
// Exact Taylor/variance constants, plus deterministic toy quadrature. No samples or keys.
let checks=0;
function gcd(a,b){return b?gcd(b,a%b):abs(a);}
function abs(a){return a<0n?-a:a;}
function f(n,d=1n){n=BigInt(n);d=BigInt(d);const g=gcd(n,d);return[n/g,d/g];}
const add=(a,b)=>f(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const mul=(a,b)=>f(a[0]*b[0],a[1]*b[1]);
const eq=(a,b)=>{checks++;if(a[0]*b[1]!==a[1]*b[0])throw Error(a+' != '+b);};
const I2=f(1,24),I4=f(1,1920),mix=f(1,576),delta=f(1,12);
const adj2=mul(f(-1,2),delta),adj4=mul(f(1,8),mul(delta,delta));
const cross=add(mul(I2,adj2),adj4);
eq(add(I2,adj2),f(0));eq(add(mix,mul(f(2),cross)),f(0));
eq(add(I4,cross),f(-1,2880));
eq(mul(f(2),mul(I2,I2)),f(1,288));eq(mul(f(24),f(1,2880**2)),f(1,345600));
const B=[[9,-3,0,3],[-3,9,-3,0],[0,-3,9,-3],[3,0,-3,9]];
const A3=[[3,1,0,-1],[1,3,1,0],[0,1,3,1],[-1,0,1,3]];
for(let i=0;i<4;i++)for(let j=0;j<4;j++)eq(f(A3[i].reduce((s,x,k)=>s+x*B[k][j],0)),f(i===j?21:0));
eq(f(B.flat().reduce((s,x)=>s+x*x,0),49),f(396,49));
eq(f(B.flat().reduce((s,x)=>s+x**4,0),2401),f(26892,2401));
// Quadrature over the half-width unit interval: eight-point Gauss-Legendre.
const X=[.1834346424956498,.5255324099163290,.7966664774136267,.9602898564975363];
const W=[.3626837833783620,.3137066458778873,.2223810344533745,.1012285362903763];
function chi(s,c,mu=0,Q=0){
 const s0=Math.sqrt(s*s-(c?1/12:0));
 const p=new Map(),q=new Map();let norm=0;
 for(let k=Math.floor(mu-12*s);k<=Math.ceil(mu+12*s);k++){
  const z=k-mu,a=Math.exp(-.5*(z/s)**2)/(Math.sqrt(2*Math.PI)*s);
  let b=0;
  for(let i=0;i<4;i++)for(const sign of [-.5,.5])b+=W[i]/2*Math.exp(-.5*((z+sign*X[i])/s0)**2)/(Math.sqrt(2*Math.PI)*s0);
  const key=Q?(k%Q+Q)%Q:k;
  q.set(key,(q.get(key)||0)+a);p.set(key,(p.get(key)||0)+b);norm+=a;
 }
 let t=0;
 for(const [k,w] of q){const a=w/norm,b=p.get(k);t+=(b-a)**2/a;}
 return t;
}
const vals=[];
for(const c of [0,1])for(const mu of [0,.37])for(const s of [8,16]){
 const r=c?8:4,v=c?1/345600:1/288,factor=s**r/v;
 const ans=chi(s,c,mu)*factor,small=chi(s,c,mu,3*s)*factor;
 if(Math.abs(ans-1)>0.035||!(small>0&&small<ans))throw Error('toy calculation');
 vals.push({compensated:!!c,mu,s,scaledChi:ans,scaledChiModulo:small});
}
console.log({exactRationalChecks:checks,toyQuadrature:vals});
