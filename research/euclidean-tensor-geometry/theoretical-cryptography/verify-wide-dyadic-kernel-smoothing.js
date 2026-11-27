/* Node 18+. Only synthetic coefficient identities and scalar Gaussian integrals. */
'use strict';
let exact=0,numeric=0;
function ex(x,l){++exact;if(!x)throw Error(l);}
function nu(x,l){++numeric;if(!x)throw Error(l);}
let seed=209182710;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
function rotation(x,d,j){
  const z=Array(x.length).fill(0);
  for(let k=0;k<x.length;++k){
    const i=k%d,zj=i+j;
    z[k-i+(zj%d)]=(zj<d?1:-1)*x[k];
  }
  return z;
}
function dot(x,y){return x.reduce((s,e,i)=>s+e*y[i],0);}
function directMul(x,y) {
  const d=x.length,o=Array(d).fill(0);
  for(let i=0;i<d;++i)for(let j=0;j<d;++j)
    o[(i+j)%d]+=(i+j<d?1:-1)*x[i]*y[j];
  return o;
}
for(const d of [1,2,4,8,16,32]) for(let r=1;r<=3;++r)
for(let ix=0;ix<90;++ix){
  const x=Array.from({length:r*d},()=>rng(15)-7);
  const y=Array.from({length:d},()=>rng(17)-8);
  const a=Array.from({length:r*d},()=>rng(13)-6);
  let computed=Array(r*d).fill(0), moment=0;
  for(let j=0;j<d;++j) {
    const v=rotation(x,d,j),negTranspose=rotation(a,d,(d-j)%d);
    ex(dot(x,x)===dot(v,v),'signed rotations are isometries');
    ex(dot(a,v)===(j===0?1:-1)*dot(negTranspose,x),'transpose rotation identity');
    computed=computed.map((z,k)=>z+y[j]*v[k]);
    moment+=dot(a,v)**2;
  }
  for(let rr=0;rr<r;++rr) {
    const got=directMul(x.slice(rr*d,(rr+1)*d),y);
    for(let i=0;i<d;++i) ex(got[i]===computed[rr*d+i],'module multiplication columns');
  }
  ex(moment>=0,'expanded squared moment');
}
for(let trial=0;trial<18;++trial){
  const N=20+rng(10);
  const row=Array.from({length:N},()=>1+rng(2));
  const den=dot(row,row),max=Math.max(...row);
  ex(4*max*max<den,'leverage threshold for two-sparse set');
  const seen=new Set([Array(N).fill(0).join(',')]);
  function check(j,sgn,k,t) {
    const a=sgn*row[j]+(k<0?0:t*row[k]),ell=k<0?1:2;
    const image=row.map((u,i)=>den*((i===j?sgn:0)+(i===k?t:0))-a*u);
    const s=image.join(',');
    ex(!seen.has(s),'sparse projected points distinct');
    ex(dot(image,image)===den*(ell*den-a*a),'exact projected squared length');
    ex(dot(row,image)===0,'exact orthogonality');
    seen.add(s);
  }
  for(let j=0;j<N;++j)for(const x of [-1,1]){
    check(j,x,-1,0);
    for(let k=j+1;k<N;++k)for(const y of [-1,1])check(j,x,k,y);
  }
}
for(let e=1n;e<=256n;++e)for(let b=1n;b<=e;++b) {
  // e >= b and C <= b/16 imply e >= b/8+(3/4)(e+C).
  ex(64n*e>=8n*b+48n*e+3n*b,'large-region exponent split');
}
function shiftLogRatio(t,a){
  let z=0;
  for(let k=1;k<=8;++k)z+=Math.exp(-t*(k*k+2*k*a))+Math.exp(-t*(k*k-2*k*a));
  return Math.log1p(z);
}
for(const s of [1,1.025,1.1,1.5,2,3,4,8,16,32,64])for(let j=0;j<=4096;++j){
  const a=.5*j/4096,t=2*Math.PI**2*s*s;
  const logPhi=-t*a*a+shiftLogRatio(t,a)-shiftLogRatio(t,0);
  nu(logPhi<=-t*a*a/3+2e-14,'periodic scalar characteristic bound');
}
function cubicProfile(N,t){
  const u=2*N*Math.exp(-t);
  return Math.expm1(u);
}
/*
 For synthetic row A=(1,...,1), Poisson projection is the dual of A_{N-1}.
 Its exact total theta is sqrt(Nt/pi) times the integral over [-1/2,1/2]
 of theta_{Z}(t,a)^N. Decompose z into classes modulo Z(1,...,1)
 and integrate the row component over all of R to verify this identity.
 The zero Gaussian part is subtracted inside the interval.
*/
function hyperplaneMass(N,t){
  const T=Math.min(14,Math.sqrt(N*t)/2),n=8192;
  let out=0;
  for(let i=0;i<n;++i){
    const u=T*(i+.5)/n;
    const a=u/Math.sqrt(N*t);
    out+=Math.exp(-u*u)*Math.expm1(N*shiftLogRatio(t,a));
  }
  const omittedBaseBound=Math.exp(-T*T)/(T*Math.sqrt(Math.PI));
  return [out*2*T/(n*Math.sqrt(Math.PI)),omittedBaseBound];
}
for(const N of [128,256,1024,4096,16384,65536])
for(const c of [-1,0,1,3,Math.log(N),Math.log(N)**1.32]){
  const t=Math.log(N)+c,[got,tail]=hyperplaneMass(N,t),want=cubicProfile(N,t);
  nu(tail/want<1e-20,'Gaussian baseline tail below plotted mass');
  const relative=Math.abs(got/want-1);
  nu(relative<=20*((1+t)/N),'hyperplane theta shape cross-check');
  if(N>=16384)console.log('N',N,'offset',c.toFixed(3),'relative profile difference',relative.toExponential(3));
}
console.log('wide kernel smoothing:',exact,'exact checks;',numeric,'deterministic numeric checks');
