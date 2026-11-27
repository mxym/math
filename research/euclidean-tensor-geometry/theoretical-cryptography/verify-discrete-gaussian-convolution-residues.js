'use strict';
// Exact lattice shell checks, then deterministic toy standalone-noise sums.
let checks=0;
function ok(x){checks++;if(!x)throw Error('check failed')}
const tuple=(lo,hi,n,fn)=>{function go(a){if(a.length===n){fn(a);return}for(let x=lo;x<=hi;x++)go([...a,x])}go([])};
for(let n=2;n<=6;n++){
 const shell=new Set();
 tuple(-2,2,n-1,a=>{
  a.push(0);const sum=a.reduce((s,x)=>s+x,0),y=a.map(x=>n*x-sum),norm=y.reduce((s,x)=>s+x*x,0);
  ok(norm===0||norm>=n*(n-1));
  if(norm===n*(n-1))shell.add(y.join());
 });
 ok(shell.size===(n===2?2:2*n));
 const multiplicity={};for(const y of shell){const v=((+y.split(',')[0])%n+n)%n;multiplicity[v]=(multiplicity[v]||0)+1}
 ok(Object.values(multiplicity).reduce((a,x)=>a+x*x,0)===(n===2?4:2*n*n));
}
for(const q of [3,5,7,9,11]){
 const h=(q+1)/2;let weights=Array(q).fill(0);
 for(const v of [-1,1])for(const t of [-1,1]){const a=(q*v+t)/2;weights[(a%q+q)%q]++;}
 ok(weights[h]===2&&weights[q-h]===2&&weights.reduce((s,v)=>s+v*v,0)===8);
}
const illustration=[];
for(const s of [1.3,1.9,2.6,3.2])for(const q of [0,3,5,6]){
 const M=30,g=k=>Math.exp(-Math.PI*k*k/(2*s*s)),f=k=>Math.exp(-Math.PI*k*k/(s*s));
 const key=x=>q?(x%q+q)%q:x;
 let total=0,base=new Map(),tilt=new Map(),z=0;
 for(let t=-M;t<=M;t++)z+=f(t);
 for(let x=-M;x<=M;x++){
  const k=key(x);total+=g(x);base.set(k,(base.get(k)||0)+g(x));
  let u=0;for(let a=-M;a<=M;a++)u+=f(a)*f(x-a);
  tilt.set(k,(tilt.get(k)||0)+u/(z*z));
 }
 let chi=0;for(const [k,v] of base){let x=v/total,delta=(tilt.get(k)-x);if(x>1e-200)chi+=delta*delta/x;}
 const factor=q%2?8*Math.exp(-Math.PI*s*s*(1+1/q**2)):4*Math.exp(-Math.PI*s*s);
 if(s===3.2 && !(chi/factor>.92&&chi/factor<1.02))throw Error('illustration '+[s,q,chi/factor]);illustration.push([s,q,chi/factor]);
}
console.log({exactAlgebraChecks:checks,illustration});
