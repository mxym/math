'use strict';
const assert = require('node:assert/strict');
let exact=0,numeric=0;
for(let a=-5;a<=5;a++)for(let b=-5;b<=5;b++)
for(let c=-5;c<=5;c++)for(let d=-5;d<=5;d++){
  const x=a+c,y=b+d,z=a-c,w=b-d;
  assert((x-z)%2===0&&(y-w)%2===0);
  assert.equal((x+z)/2,a);assert.equal((x-z)/2,c);
  assert.equal((y+w)/2,b);assert.equal((y-w)/2,d);
  assert.equal(x*x+y*y+z*z+w*w,2*(a*a+b*b+c*c+d*d));exact+=6;
}
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
const plus=(a,b)=>a.map((x,i)=>x+b[i]),minus=(a,b)=>a.map((x,i)=>x-b[i]);
const scale=(a,r)=>a.map(x=>r*x);
const zero=n=>Array(n).fill(0);
function grid(B,N){
  const L=[],n=B.length;
  function go(i,v,c){
    if(i===n){L.push([v,c]);return;}
    for(let j=-N;j<=N;j++)go(i+1,plus(v,scale(B[i],j)),c|((j&1)<<i));
  }
  go(0,zero(n),0);return L;
}
function moments(L,t,z,u,v=u){
  let A=0,M=0,N=0,U2=0,V2=0,UV=0,UV2=0;
  for(const [a] of L){
    const x=plus(a,z),w=Math.exp(-t*dot(x,x)),s=dot(x,u),r=dot(x,v);
    A+=w;M+=w*s;N+=w*r;U2+=w*s*s;V2+=w*r*r;UV+=w*s*r;UV2+=w*s*s*r*r;
  }
  return {A,variance:U2/A-(M/A)**2,kappa:UV2/A-U2*V2/A**2-2*(UV/A)**2};
}
function parity(L,t,z,u,v=u){
  let h=zero(2**z.length),du=h.slice(),d2=h.slice();
  for(const [a,c] of L){
    const x=plus(a,z), w=Math.exp(-.5*t*dot(x,x)), r=dot(x,u),s=dot(x,v);
    h[c]+=w;du[c]-=t*r*w;d2[c]+=(t*t*r*s-t*dot(u,v))*w;
  }
  const length=Math.sqrt(dot(h,h)), m=scale(h,1/length);
  const tangent=d=>scale(minus(d,scale(m,dot(d,m))),1/length);
  // tangent(d2) is the mixed second jet of m only at z=0 (h'=0).
  return {h,m,du:tangent(du),d2:tangent(d2)};
}
const near=(a,b,e=2e-11)=>{assert(Math.abs(a-b)<e,[a,b]);numeric++;};
const sets=[
  [[[1]],12], [[[1,0],[.5,Math.sqrt(3)/2]],12], [[[1,0],[0,1.4]],12],
  [[[1,0,0],[.5,Math.sqrt(3)/2,0],[0,0,1.2]],11]
];
for(const [B,N] of sets){
  const d=B.length,L=grid(B,N);
  for(const t of [.85,1.6,2.8]) for(let r=0;r<9;r++){
    const arr=f=>Array.from({length:d},(_,j)=>f(j));
    const z=arr(j=>.28*Math.sin(1.17*r+.71*j+.18));
    const y=arr(j=>.22*Math.cos(.97*r-.31*j+.12));
    const u=arr(j=>.6*Math.cos(.34*r+.73*j+.42)),v=arr(j=>.5*Math.sin(.29*r-.63*j+.92));
    const O=moments(L,t,zero(d),u,v), M=moments(L,t,z,u);
    const J=parity(L,t,z,u), H=parity(L,t,zero(d),u,v);
    near(M.variance-O.variance,dot(J.du,J.du)/t**2);
    near(O.kappa,dot(H.d2,H.d2)/(2*t**4));
    near(dot(J.h,J.h),M.A*O.A);
    const P=parity(L,t,plus(z,y),u), Q=parity(L,t,minus(z,y),u);
    const Y=moments(L,t,y,u), Zp=moments(L,t,plus(z,y),u), Zm=moments(L,t,minus(z,y),u);
    near(dot(P.h,Q.h),M.A*Y.A);
    near(Math.log(O.A**2*Zp.A*Zm.A/(M.A*Y.A)**2),-2*Math.log(dot(P.m,Q.m)));
    assert(M.variance>=O.variance-1e-14&&O.kappa>=-1e-14);numeric+=2;
  }
}
const square=grid([[1,0],[0,1.4]],12), t=1.9;
near(moments(square,t,[0,.4],[1,0]).variance,moments(square,t,[0,0],[1,0]).variance);
near(moments(square,t,[0,0],[1,0],[0,1]).kappa,0);
const hx=parity(square,t,[.2,.31],[1,0]).m, hy=parity(square,t,[.2,-.31],[1,0]).m;
near(dot(hx,hy),1);
const hex=grid([[1,0],[.5,Math.sqrt(3)/2]],12);
const J=parity(hex,t,[.18,-.22],[1,0]), K=parity(hex,t,[.18,-.22],[0,1]);
assert(dot(J.du,J.du)*dot(K.du,K.du)-dot(J.du,K.du)**2>1e-8);
assert(moments(hex,t,[0,0],[1,0],[0,1]).kappa>1e-5);numeric+=2;
console.log('PASS',exact,'exact parity checks and',numeric,'numerical covariance/jet identity checks');
