'use strict';
const assert=require('node:assert/strict');
let exact=0,numeric=0;
function check(a,msg){assert(a,msg);exact++;}
function near(x,y,t=1e-9){assert(Number.isFinite(x)&&Math.abs(x-y)<=t*Math.max(1,Math.abs(y)),[x,y,t].join(' '));numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const sym=n=>Array.from({length:2*n+1},(_,i)=>i-n);
const mod=(a,n)=>(a%n+n)%n;
for (let a=2;a<=8;a++) for(let b=-2;b<=2;b++) for(let c=2;c<=7;c++){
 if(a*c<=b*b)continue;
 const form=(x,y)=>a*x*x+2*b*x*y+c*y*y;
 const q=[[0,0],[1,2],[-3,1],[2,-3],[-2,-1]];
 for(let r=2;r<=9;r++)for(const x of q)for(const v of q){
  const k=v.map(i=>r*i),z=x.map((i,j)=>i+k[j]);
  const two=x.map((i,j)=>2*i+k[j]);
  check(2*(form(...x)+form(...z))===form(...two)+form(...k));
 }
}
const vb=[[1,0],[0,1],[-1,1]];
for(const [a,b] of vb){
 const bil=(x,y)=>2*a*x+a*y+b*x+2*b*y;
 const exactHalfWitness=sym(3).some(x=>sym(3).some(y=>2*bil(x,y)===bil(a,b)));
 check(exactHalfWitness);
}
for(const r of seq(15).map(x=>x+3))for(const theta of [0.35,0.55,0.74,1.04]) {
 const src=seq(r).map(s=>sym(7).reduce((a,k)=>a+Math.exp(-(Math.PI**2)/theta*(s/r+k)**2),0));
 const amp=seq(r).map(y=>sym(8).reduce((a,k)=>a+Math.exp(-theta*(y+r*k)**2),0));
 for(let y=0;y<r;y++){
  let re=0,im=0;
  for(let s=0;s<r;s++){
   const u=2*Math.PI*s*y/r;
   re+=src[s]*Math.cos(u)/r;im+=src[s]*Math.sin(u)/r;
  }
  near(re,Math.sqrt(theta/Math.PI)*amp[y],2e-13);
  near(im,0,2e-13);
 }
}
function oneDim(r,t){
 const Z=sym(35).reduce((a,k)=>a+Math.exp(-2*t*k*k),0);
 const q=seq(r).map(y=>sym(5).reduce((a,k)=>a+Math.exp(-2*t*(y+r*k)**2),0)/Z);
 const c=seq(r).map(y=>{
  let z=0;
  for(let v=1;v<=6;v++){
   const a=sym(5).reduce((a,k)=>a+Math.exp(-2*t*(y+r*k+r*v/2)**2),0);
   z+=2*Math.exp(-t*r*r*v*v/2)*a/Z;
  }
  return z;
 });
 const d=c.reduce((x,y)=>x+y,0);
 const tv=c.reduce((a,z,y)=>a+Math.abs(z-d*q[y]),0)/(2*(1+d));
 const chi=c.reduce((a,z,y)=>a+q[y]*((z/q[y]-d)/(1+d))**2,0);
 return {Z,q,c,d,tv,chi};
}
for(const t of [0.35,0.72,1.05])for(const r of [20,21,22,23,24,25]) {
 const b=Math.exp(-t*r*r/2), {Z,q,c,d,tv,chi}=oneDim(r,t);
 const Zpar=sym(35).reduce((a,k)=>a+Math.exp(-2*t*(k+(r%2)/2)**2),0);
 near(d/b,2*Zpar/Z,1e-12);near(tv/b,2*Zpar/Z,2e-6);
 if(r%2)near(chi/(b*Math.exp(-t*r)),8*Math.exp(-t/2)/Z,2e-6);
 else {
  near(q[r/2]/b,2/Z,1e-12);near(c[r/2]/q[r/2],1,1e-12);
  near(chi/b,2/Z,2e-6);
 }
}
// In nonorthogonal A2 the odd mesh still has active exact bisectors.
for(const r of [12,13,14,15]){
 const Q=(x,y)=>x*x+x*y+y*y,th=1.0;
 const V=sym(4).flatMap(x=>sym(4).map(y=>[x,y])).filter(([x,y])=>x||y);
 const ZZ=sym(12).flatMap(x=>sym(12).map(y=>[x,y])).reduce((a,v)=>a+Math.exp(-2*th*Q(...v)),0);
 const d=Math.exp(-th*r*r/2);
 let c2q=0, kap=0;
 for(const [v,w] of vb) for(const i of sym(20))for(const j of sym(20)){
  const x=2*i-(r%2)*v,y=2*j-(r%2)*w;
  if((2*v+w)*x+(v+2*w)*y===0)
    kap+=2*Math.exp(-th*Q(x,y)/2)/ZZ;
 }
 for(let x=0;x<r;x++)for(let y=0;y<r;y++){
   let q=0,c=0;
   for(const i of sym(3))for(const j of sym(3))q+=Math.exp(-2*th*Q(x+r*i,y+r*j))/ZZ;
   for(const [v,w] of V){
    const factor=Math.exp(-th*r*r*Q(v,w)/2)/ZZ;
    if(factor===0)continue;
    for(const i of sym(3))for(const j of sym(3))
       c+=factor*Math.exp(-2*th*Q(x+r*i+r*v/2,y+r*j+r*w/2));
   }
   c2q+=c**2/q;
 }
 assert(kap>0);
 near(c2q/d,kap,0.00003);
}
console.log('PASS: '+exact+' exact and '+numeric+' numerical checks');
