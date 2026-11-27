"use strict";

// Small fixed synthetic lattices and scalar formulas; no random-Haar evidence is used.
const pi=Math.PI, ab=Math.abs;
let exact=0,numerics=0;
function check(a,label){if(!a) throw new Error(label);++exact;}
function near(x,y,e,label) {
 if(!Number.isFinite(x)||!Number.isFinite(y)||ab(x-y)>e*Math.max(1,ab(x),ab(y)))
    throw new Error(label+": "+x+" vs "+y);
 ++numerics;
}
const dot=(a,b)=>a.reduce((t,v,i)=>t+v*b[i],0);
const q=a=>dot(a,a);
const mul=(A,v)=>A.map(row=>dot(row,v));
const add=(a,b)=>a.map((x,i)=>x+b[i]);
const zeros=k=>new Array(k).fill(0);
function dual(A){
 const d=A.length;
 const T=Array.from({length:d},(_,i)=>A[i].concat(zeros(d).map((_,j)=>+(i===j))));
 let det=1;
 for(let i=0;i<d;i++){
   const x=T[i][i];det*=x;
   for(let j=0;j<2*d;j++)T[i][j]/=x;
   for(let j=0;j<d;j++)if(j!==i){
     const c=T[j][i];for(let h=0;h<2*d;h++)T[j][h]-=c*T[i][h];
   }
 }
 return {B:Array.from({length:d},(_,j)=>Array.from({length:d},(_,i)=>T[i][j+d])),v:det};
}
function box(A,r){
 const d=A.length,X=zeros(d),V=[];
 function walk(i){
   if(i===d){V.push(mul(A,X));return;}
   for(let j=-r;j<=r;j++){X[i]=j;walk(i+1);}
 }
 walk(0);return V;
}
function expDivExp(delta,E) {
 return delta===0?E:Math.expm1(delta*E)/delta;
}
function logDivLog(delta,E) {
 return delta===0?E:Math.log1p(delta*E)/delta;
}
const expRatio = x => x===0?1:Math.expm1(x)/x;
for(const A of [
 [[1.1]], [[0.74]], [[1,0.35],[0,0.84]], [[1.22,-0.64],[0,0.71]],
 [[1,0.25,-0.33],[0,1.03,0.18],[0,0,0.9]]
]){
 const n=A.length,{B,v}=dual(A),X=box(A,12),F=box(B,8);
 for(const s of [1.1,1.53,2.02]) {
  const T=F.map(y=>pi*s*s*q(y)),w=T.map(t=>Math.exp(-t));
  const R=w.reduce((a,x,j)=>a+(T[j]>0?x:0),0);
  for(const t of [.12,.33,.48]) {
    const rat=w.reduce((s,x,j)=>s+Math.exp(-(1-t)*T[j]),0)/(1+R);
    if(!(rat<=(1-t)**(-n/2)+1e-12))throw new Error("radial MGF bound");
    ++numerics;
  }
  for(const shift of [0,0.07,0.49,0.93]){
   const z=zeros(n).map((_,i)=>shift*Math.cos(0.86*i));
   const E=X.map(x=>pi*q(add(x,z))/(s*s)), W=E.map(e=>Math.exp(-e));
   const Z=W.reduce((a,b)=>a+b), S=F.map(y=>Math.cos(2*pi*dot(y,z)));
   const theta=1+w.reduce((a,p,j)=>a+(T[j]>0?p*S[j]:0),0);
   near(Z,s**n*theta/v,5e-12,"Poisson shift and covolume");
   for(const alpha of [.77,.9999999997,1,1.0000000002,1.02,1.26,1.97]){
     const d=alpha-1,a=d/alpha;
     const Entropy=Math.log(Z)-logDivLog(d,
       W.reduce((r,x,i)=>r+x*expDivExp(d,-E[i]),0)/Z);
     const h=n*Math.log(s)+n/2*logDivLog(d,1);
     const dif=-Math.log(v)+h-Entropy;
     // d==0 yields the theta derivative. Otherwise use log1p for tiny d.
     const D=w.reduce((r,x,j)=>r+S[j]*(Math.abs(a*T[j])<=0.5?
       x*expDivExp(d,T[j]/alpha):(Math.exp(-T[j]/alpha)-x)/d),0);
     const f=logDivLog(d,D/theta)-Math.log(theta);
     near(dif,f,5e-10,"entropy and theta difference quotient");
     if(alpha>0.7&&R<0.1){
       const t=0.68,K=(Math.log((1+R)/R)+(n/2)*Math.log(1/(1-t)))/t;
       if(!(ab(D)<=R*expDivExp(d,K/alpha)+1e-12))throw new Error("theta quotient bound");
       ++numerics;
     }
   }
  }
 }
}
for(let p=1n;p<=100n;p++) for(let q=1n;q<=100n;q++) {
 const x=p*p+q*q;
 check(4n*p*p*q*q<=x*x,"Gaussian radial p^2q^2 ratio");
}
for(let j=1;j<=12;j++) for(const t of [.52,1.13,5.7]) {
  // Gamma radial integral at real dimension 2j. Direct quadrature after y=tT.
  const N=64000, L=115, h=L/N;
  let gamma=1;for(let k=2;k<j;k++)gamma*=k;
  for(const r of [0,1,2]){
   let ord=1;for(let k=0;k<r;k++)ord*=j+k;
   let sum=0;
   for(let i=0;i<=N;i++){
     const a=i*h, w=i===0||i===N?1:i%2===0?2:4;
     sum+=w*a**(j-1+r)*Math.exp(-a);
   }
   const power=t**(j+r);
   near(sum*h/(3*gamma*power),ord/power,2e-9,"radial energy integral");
  }
}
for (const b of [10,20,40,80,150,400]) for(const n of [1,2,5,12]) {
 const eps=Math.exp(-b),t1=b+Math.log(2)+Math.sqrt(eps);
 const t2=4*b+Math.log(2*n), e1=Math.exp(-t1);
 function stepRatio(E,delta,alpha) {
   let a=0,b=0;
   for(let j=1;j<=6;j++) {
     const T=E*j*j,w=Math.exp(-T);
     if(w!==0){a+=2*w;b+=2*w*expDivExp(delta,T/alpha);}
   }
   return [Math.log1p(a),b/(1+a)];
 }
 const q0=stepRatio(t1,0,1)[0]+(n-1)*stepRatio(t2,0,1)[0];
 if(!(Math.expm1(q0)<=eps*(1+1e-12)))throw new Error("two-atom smoothing budget");
 ++numerics;
 for(const u of [-2,-.7,0,.00001,.4,1.7,3]){
   const d=u/b,alpha=1+d;
   const v=2*e1*expDivExp(d,t1/alpha)/(eps*b);
   if(b>=150)near(v,expRatio(u),0.09,"two-atom window");
   const z=stepRatio(t1,d,alpha),q=stepRatio(t2,d,alpha);
   const slope=logDivLog(d,z[1])+(n-1)*logDivLog(d,q[1]);
   near(slope/(eps*b),v,0.001,"two-atom quotient");
 }
}
for(const n of [16,38,128,1000,10000,1000000])for(const eps of [.01,.05,.5]) {
 for(const u of [-3,-1,-1e-5,0,1e-5,.3,3]){
   const h=u/n, a=n/2*Math.log1p(h);
   const alt=logDivLog(u,(eps/(1+eps))*expRatio(a)*(h===0?0.5:a/u));
   const lim=logDivLog(u,(eps/(1+eps))*0.5*expRatio(u/2));
   if(Math.abs(u)>5e-6)near(alt,(Math.log1p(eps*(1+h)**(n/2))-Math.log1p(eps))/u,
        5e-6,"dimension-window mean");
   if(n>=1000000)near(alt,lim,2e-6,"dimension-window limit");
 }
}
console.log(exact+" exact algebraic checks; "+numerics+
            " deterministic numerical checks: PASS");
