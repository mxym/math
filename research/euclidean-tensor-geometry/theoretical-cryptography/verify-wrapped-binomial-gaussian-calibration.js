'use strict';
const assert=require('node:assert/strict');let exact=0,numeric=0;
function ck(b,m){assert(b,m);exact++;}
function near(a,b,t=1e-9){assert(Number.isFinite(a)&&Math.abs(a-b)<=t*Math.max(1,Math.abs(b)),[a,b,t].join(' '));numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const sym=n=>Array.from({length:2*n+1},(_,i)=>i-n);
const mod=(a,q)=>(a%q+q)%q;
function binrow(n){const out=[1n];for(let j=1;j<=n;j++)out.push(out[j-1]*BigInt(n-j+1)/BigInt(j));return out;}
for(let m=1;m<=44;m++)for(let q=2;q<=20;q++){
 const r=Array(q).fill(0n);
 for(const [j,v] of binrow(2*m).entries())r[mod(j-m,q)]+=v;
 let w=Array(q).fill(0n);w[mod(-m,q)]=1n;
 for(let j=0;j<2*m;j++)w=w.map((u,i)=>u+w[mod(i-1,q)]);
 for(let i=0;i<q;i++)ck(r[i]===w[i]&&w[i]===w[mod(-i,q)]);
 ck(w.reduce((u,v)=>u+v,0n)===2n**BigInt(2*m));
 const Z=2**(2*m);
 for(let j=0;j<q;j++){
  const re=r.reduce((u,v,i)=>u+Number(v)/Z*Math.cos(2*Math.PI*j*i/q),0);
  const im=r.reduce((u,v,i)=>u+Number(v)/Z*Math.sin(2*Math.PI*j*i/q),0);
  near(re,Math.cos(Math.PI*j/q)**(2*m),3e-13);near(im,0,3e-13);
 }
}
for(const b of [0.22,0.69,1.33,2.3,6.7,13.3,31.1])for(const t of [-2.4,-0.128,0.35,1.13,3.96])for(const q of [3,6,7,11,17]){
 const ks=sym(70),p=ks.map(x=>Math.exp(-((x-t)**2)/b)),Z=p.reduce((u,v)=>u+v,0);
 const d=sym(35).reduce((u,v)=>u+Math.exp(-(Math.PI**2)*b*v*v)*Math.cos(2*Math.PI*v*t),0);
 for(const j of seq(q).map(i=>i-Math.floor(q/2))){
  const k=j/q;
  const lhsRe=ks.reduce((u,v,i)=>u+p[i]*Math.cos(2*Math.PI*k*v),0)/Z;
  const lhsIm=ks.reduce((u,v,i)=>u+p[i]*Math.sin(2*Math.PI*k*v),0)/Z;
  const rhsRe=sym(35).reduce((u,v)=>u+Math.exp(-(Math.PI**2)*b*(v-k)**2)*Math.cos(2*Math.PI*(k-v)*t),0)/d;
  const rhsIm=sym(35).reduce((u,v)=>u+Math.exp(-(Math.PI**2)*b*(v-k)**2)*Math.sin(2*Math.PI*(k-v)*t),0)/d;
  near(lhsRe,rhsRe,8e-14);near(lhsIm,rhsIm,8e-14);
 }
}
for(const q of [17,24,31,47,73,103])for(const r of [1.7,2.3,3.1,4.6,7.7]) {
 const m=Math.floor(r*q*q),x=Math.PI/q,a=m*x*x,mu=-2*m*Math.log(Math.cos(x));
 const k=-2*m*Math.log(Math.cos(2*x))-4*mu,D=Math.exp(-4*mu)*(-Math.expm1(-k));
 const D1=Math.exp(-a)*(-Math.expm1(-mu+a));
 ck(mu>a&&k>0);
 for(const [v,d,j0] of [[a,D1,1],[mu,D,2]]){
  const A=sym(Math.floor(q/2)).filter(j=>j>=-Math.floor((q-1)/2)).map(j=>{
    const u=Math.abs(j);
    if(u<j0)return [j,0];
    const rate=-2*m*Math.log(Math.abs(Math.cos(j*x)));
    return [j,Math.exp(-v*j*j)*(-Math.expm1(-rate+v*j*j))/d];
  });
  const mass=A.reduce((u,[j,v])=>u+(Math.abs(j)>j0?Math.abs(v):0),0);
  assert(mass<2e-4);numeric++;
  for(let y=0;y<q;y++){
   const s=A.reduce((u,[j,v])=>u+v*Math.cos(2*Math.PI*j*y/q),0);
   near(s,2*Math.cos(2*Math.PI*j0*y/q),4e-4);
  }
 }
 assert(D/D1<=20*Math.exp(-3*a));numeric++;
}
console.log('PASS: '+exact+' exact/structural and '+numeric+' numerical checks');
