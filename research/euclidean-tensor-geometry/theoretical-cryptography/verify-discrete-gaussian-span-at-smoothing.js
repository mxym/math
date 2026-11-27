"use strict";

// No packages. Only deterministic generated lattices and elementary inequalities.
// This replay is a check on normalizations/constants, not an inference from data.
const pi = Math.PI, c2 = Math.sqrt(2 * pi);
let exact = 0, numeric = 0;
function check(x, label, isExact = false) {
  if (!x) throw new Error(label);
  if (isExact) ++exact; else ++numeric;
}
function near(x, y, tol, label) {
  check(Number.isFinite(x) && Number.isFinite(y) &&
        Math.abs(x-y) <= tol * Math.max(1, Math.abs(x), Math.abs(y)),
        label + ": " + x + " vs " + y);
}
const dot = (x,y) => x.reduce((s,v,i) => s+v*y[i],0);
const sq = x => dot(x,x);
const add = (x,y) => x.map((v,i)=>v+y[i]);
const sub = (x,y) => x.map((v,i)=>v-y[i]);
const sc = (x,t) => x.map(v=>v*t);
const mv = (B,x) => B.map(r=>dot(r,x));
function reciprocal(B) {
  if (B.length === 1) return {d: B[0][0], C: [[1/B[0][0]]]};
  const [[a,b],[c,d]]=B, det=a*d-b*c;
  return {d:det,C:[[d/det,-c/det],[-b/det,a/det]]};
}
function lattice(B,M) {
  const out=[];
  if(B.length===1) for(let i=-M;i<=M;i++) out.push(mv(B,[i]));
  else for(let i=-M;i<=M;i++) for(let j=-M;j<=M;j++)
    out.push(mv(B,[i,j]));
  return out;
}
function cm(old,w,t) { old[0]+=w*Math.cos(t); old[1]+=w*Math.sin(t); }
const qval=(axes,x)=>axes.reduce((s,v)=>s+dot(v,x)**2,0);
const proj=(axes,x)=>axes.reduce((y,v)=>add(y,sc(v,dot(v,x))),
                                 x.map(()=>0));

for (let q=2; q<=128; q++) {
  const den=BigInt(q);
  for(let p=0;p*2<=q;p++) {
    const num=BigInt(p);
    // x^2/[2(1-x)] <= x^2 for 0<=x<=1/2 by cross multiplication.
    check(num*num*den <= 2n*num*num*(den-num), "log remainder", true);
  }
}
for(let q=1;q<=72;q++) for(let p=0;p*8<=7*q;p++) {
  const d=BigInt(q), z=BigInt(p);
  // For geometric failures with p<=7/8, their mean <= 8p.
  check(z*d <= 8n*z*(d-z), "conditional geometric mean", true);
  // For e^t=9/8: (1-p)/(1-e^t p)-1 <= 8p.
  check(64n*d-72n*z>=d, "conditional mgf bound", true);
}
for(let k=100000;k<=10000000;k=Math.floor(k*1.019)+1) {
  const ell=Math.log1p(k), a=Math.exp(-4*ell/k), h=-Math.expm1(-4*ell/k);
  const r=k/(64*ell*ell);
  check(r>=2 && r*h<0.5 && k*r*h*h/2<=0.125+1e-12, "r,h constraints");
  near(a**(k/2),(k+1)**(-2),1e-12,"leading codimension term");
  const logFactor=(-4*ell-k*Math.log1p(-r*h)/r)/2;
  check(logFactor>=-1e-11 && logFactor<=0.125+1e-11,"Hölder factor");
}
for(let b=8;b<=1e6;b*=1.073) {
  const eps=Math.exp(-b);
  check((1+(1+eps)*Math.exp(-b/4))/(1-eps)<2,"low frequency");
  check(Math.exp(-0.5)*(1+(1+eps)*Math.sqrt(eps)*Math.E)/(1-eps)<0.75,
        "unit frequency");
  check(2*(eps/4)/(1-eps/4)<=eps,"one-dimensional dual tail");
}

const examples=[
 [[1]],
 [[1.4]],
 [[1,0.22],[0.1,1.08]],
 [[1.2,-0.28],[0.17,0.83]],
 [[0.88,0.35],[-0.12,1.1]]
];
for(const B of examples) {
  const n=B.length, {d,C}=reciprocal(B), X=lattice(B,23), F=lattice(C,9);
  const axesSet = n===1 ? [[[1]]] : [
    [[1,0]], [[0,1]], [[3/5,4/5]], [[-5/13,12/13]],
    [[3/5,4/5],[-4/5,3/5]]
  ];
  for(const s of [2.5,2.8,3.4]) {
    const ss=pi*s*s, fr=F.map(y=>Math.exp(-ss*sq(y)));
    const theta=fr.reduce((a,v)=>a+v,0), eps=theta-1;
    check(eps<Math.exp(-8),"toy smoothing");
    for (const sh of [0,0.21,0.63]) {
      const c=n===1?[sh]:[sh,-0.43*sh], norm=[], shifts=[];
      let thetaC=0,rho=0;
      for(let i=0;i<F.length;i++) thetaC+=fr[i]*Math.cos(2*pi*dot(F[i],c));
      for(const x of X) {
        const z=sc(sub(x,c),c2/s), w=Math.exp(-sq(z)/2);
        rho+=w; norm.push(z); shifts.push(w);
      }
      near(rho,s**n*thetaC/d,2e-12,"shifted Poisson mass");
      for(const uv of [0,0.2,0.53,0.91,1.25,-1.11]) {
        const u=n===1?[uv]:[uv,-uv*0.3], primal=[0,0],dual=[0,0];
        for(let i=0;i<X.length;i++) cm(primal,shifts[i],dot(u,norm[i]));
        for(let i=0;i<F.length;i++) cm(dual,
          Math.exp(-ss*sq(sub(F[i],sc(u,1/(c2*s))))),-2*pi*dot(F[i],c));
        for(let j=0;j<2;j++) near(primal[j]/rho,dual[j]/thetaC,2e-12,
                                 "modulated Poisson");
      }
      for(const axes of axesSet) for(const a of [0.25,0.5,0.81,0.957]) {
        const k=axes.length,h=1-a;
        for(const shift of [0,0.42]) {
          const z0=sc(axes[0],shift), factor=Math.exp(-h*sq(z0)/2)*a**(k/2)/thetaC;
          let left=0,right=0;
          for(let i=0;i<X.length;i++) left+=shifts[i]*
            Math.exp(-(1/a-1)*sq(sub(proj(axes,norm[i]),z0))/2);
          const center=add(c,sc(z0,h*s/c2));
          for(let i=0;i<F.length;i++) {
            const f=F[i];
            right+=Math.exp(-ss*(sq(f)-h*qval(axes,f)))*Math.cos(2*pi*dot(f,center));
          }
          near(left/rho,factor*right,2e-12,"anisotropic shifted Poisson");
        }
      }
    }
  }
}
for (let j=-103;j<=103;j++) {
  const x=j/11,B=1.6, N=4000, dt=B/N;
  let rhs=0;
  for(let i=0;i<=N;i++) {
    const w=i===0||i===N?1:i%2===0?2:4,t=i*dt;
    rhs+=w*(1-t/B)*Math.cos(t*x);
  }
  rhs*=2*dt/(3*B);
  const z=B*x/2, lhs=z===0?1:(Math.sin(z)/z)**2;
  near(lhs,rhs,8e-11,"Fejer normalization");
}
for (const ps of [[1/8],[1/8,1/3,1/2],[1/50,1/10,3/5,7/8]]) {
  const g=1.06;
  let p0=1, transform=1, mean=0;
  for(const p of ps) {
    let pp=1-p, a=0,b=0, c=0;
    for(let k=0;k<600;k++,pp*=p) { a+=pp; b+=pp*k; c+=pp*g**k; }
    near(a,1,2e-13,"geometric mass");
    near(b,p/(1-p),2e-13,"geometric mean");
    near(c,(1-p)/(1-g*p),2e-13,"geometric transform");
    mean+=b; transform*=c; p0*=(1-p);
  }
  const sum=ps.reduce((a,p)=>a+p,0);
  check(1-p0<=sum && mean<=8*sum && Math.log(transform)<=8*sum,
        "rank waiting accumulation");
}
console.log(exact+" exact rational checks; "+numeric+
            " deterministic numerical/structural checks: PASS");
