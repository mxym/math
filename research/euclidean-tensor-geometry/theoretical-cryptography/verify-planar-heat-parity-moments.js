'use strict';
/* Exact shell and rational-constant checks, plus separate floating-point
 * numerical checks on generated planar shapes. No external packages. */
const assert=require('node:assert/strict');
let exact=0,numerical=0;
function ck(a,b){assert.deepEqual(a,b);exact++;}
function tr(v){assert(v);exact++;}
function close(a,b,rt=3e-11){assert(Math.abs(a-b)<=rt*Math.max(1,Math.abs(a),Math.abs(b)),String([a,b]));numerical++;}
function below(a,b,rt=3e-11){assert(a<=b+rt*Math.max(1,Math.abs(a),Math.abs(b)),String([a,b]));numerical++;}
const seq=n=>Array.from({length:n},(_,j)=>j);
const sum=a=>a.reduce((p,v)=>p+v,0);
const parity=(m,n)=>(m&1)+2*(n&1);
// Rational lower bounds on exponent and increment in (7).
tr(3*(8*81-100)>2*180*4); // (3/2)(8*(9/20)-5/9)>4.
tr(3*9*16>2*20*10);
tr(3*1024*1023+2*1024<16*1023**2); // 2^-4 sum (3+2k)2^-10k < 1.
tr(384+480+300+125>3*384); // first four terms of exp(5/4).
tr(2*2**18<3*(2**18-1));
tr(49*36<169*12); // (sqrt(3)/2+2/sqrt(3))^2 < (13/6)^2.
function shells(A,B,C,cap,aw,bw){
  const Q=(m,n)=>A*m*m+2*B*m*n+C*n*n;
  // Completing squares gives Q >= det/C * m^2 and det/A * n^2.
  const det=A*C-B*B, N=Math.ceil(Math.sqrt(2*cap*C/det)),M=Math.ceil(Math.sqrt(2*cap*A/det));
  const V=[];
  for(let m=-N;m<=N;m++)for(let n=-M;n<=M;n++){
    const q=Q(m,n);if(q<=2*cap)V.push({m,n,q,d:parity(m,n)});
  }
  const small=V.filter(v=>v.q<=cap),out=()=>Array(cap+1).fill(0);
  let c3=out(),c3half=out(),c4=out(),c4pair=out(),c4had=out();
  for(const v of small)for(const w of small){
    const s=Q(v.m+w.m,v.n+w.n);
    const t=aw*(v.q+w.q)+bw*s;
    if(t<=cap)c3[t]++;
    for(const z of small){
      const q=Q(v.m+w.m+z.m,v.n+w.n+z.n);
      const h=aw*(v.q+w.q)+bw*(z.q+q);
      if(h<=cap)c4[h]++;
    }
  }
  for(const r of V)for(const d of V){
    const t=(aw+2*bw)*r.q+aw*d.q;
    if(r.d===d.d && t<=2*cap){tr(t%2===0);c3half[t/2]++;}
    if(r.d===d.d)for(const e of V){
      const h=(aw+bw)*r.q+aw*d.q+bw*e.q;
      if(e.d===r.d&&h<=2*cap){tr(h%2===0);c4pair[h/2]++;}
    }
  }
  ck(c3,c3half);ck(c4,c4pair);
  if(aw===bw){
    for(const r of small)for(const d of small)for(const e of small)
      if((r.d^d.d^e.d)===0 && aw*(r.q+d.q+e.q)<=cap)c4had[aw*(r.q+d.q+e.q)]++;
    ck(c4,c4had);
  }
}
for(const [A,B,C] of [[1,0,1],[2,1,2],[2,1,5],[3,1,8],[9,4,9]]){
  for(const [aw,bw] of [[1,1],[1,2],[2,1],[2,3],[3,4]])shells(A,B,C,16,aw,bw);
}
// Integer sorted sequences, sharp Chebyshev reduction. Monotonicity is
// checked from the exact polynomial derivative on the feasible cone.
function rng(s){return ()=>{s=(1664525*s+1013904223)>>>0;return s/2**32;};}
const rnd=rng(27081);
for(let test=0;test<100;test++){
  const m=1+Math.floor(6*rnd()),V=seq(m).map(()=>seq(3).map(()=>BigInt(1+Math.floor(10*rnd()))).sort((a,b)=>Number(a-b)));
  const S=V.map(v=>v.reduce((a,b)=>a+b,0n)),A=V.map(v=>v[2]+1n);
  const direct=seq(3).reduce((p,i)=>p+V.reduce((s,v)=>s*v[i],1n),0n),D=3n**BigInt(m-1);
  tr(D*direct>=S.reduce((p,v)=>p*v,1n));
  for(let i=0;i<m;i++){
    const q=seq(m).filter(j=>j!==i),a=q.reduce((p,j)=>p*A[j],1n),s=q.reduce((p,j)=>p*S[j],1n);
    tr(D*a-s>=0n);
  }
}
function tv(x,y,u){
  const I=Math.ceil(Math.sqrt(82*y/u))+2,J=Math.ceil(Math.sqrt(82/(u*y)))+2,ans=[0,0,0,0];
  for(let n=-J;n<=J;n++){
    const c=-x*n;
    for(let m=Math.floor(c)-I;m<=Math.ceil(c)+I;m++){
      const q=(m-c)**2/y+y*n*n;
      ans[parity(m,n)]+=Math.exp(-u*q);
    }
  }
  return ans;
}
const xy=[[0,1],[0,5/4],[1/2,Math.sqrt(3)/2],[1/4,Math.sqrt(15)/4],[1/2,1.5],[1/2,2],[0.16,1.3],[0.49,1.5],[0.17,4]];
for(let i=0;i<230;i++){
  const x=0.5*rnd(),y=Math.sqrt(1-x*x)*Math.exp(2*rnd());
  xy.push([x,y]);
}
for(const [x,y] of xy){
  for(const u of [0.65,Math.PI/2,2.4,4.2,7.8,13.4]){
    const p=tv(x,y,u),q=tv(x,y,Math.PI**2/(4*u));
    below(p[3],p[2]);below(p[2],p[1]);below(p[1],p[0]);
    for(let i=0;i<4;i++){
      const value=sum(q.map((z,j)=>(i===0||j===0||i===j)?z:-z))*Math.PI/(4*u);
      close(p[i],value);
    }
    if(x===0.5)close(p[2],p[3]);
    if(Math.abs(x*x+y*y-1)<1e-13)close(p[1],p[2]);
  }
  for(const [u,v] of [[0.75,1.1],[0.5,4.1],[1.9,3.6],[3.4,2.5]]){
    const a=tv(x,y,u),b=tv(x,y,v),c=tv(x,y,(u+v)/2);
    const ah=tv(1/2,Math.sqrt(3)/2,u),bh=tv(1/2,Math.sqrt(3)/2,v),ch=tv(1/2,Math.sqrt(3)/2,(u+v)/2);
    below(sum(ah.map((p,j)=>p*bh[j])),sum(a.map((p,j)=>p*b[j])));
    below(sum(ah.map((p,j)=>p*bh[j]*ch[j])),sum(a.map((p,j)=>p*b[j]*c[j])));
  }
}
console.log('PASS: '+exact+' exact checks; '+numerical+' numerical checks');
