"use strict";
// Generated algebra and numerical Shannon entropy checks; no external inputs.
let exact=0,numerical=0;
function check(ok,msg,num=false){if(!ok)throw new Error(msg);if(num)++numerical;else ++exact;}
function vectors(n,R,fun){
 const x=Array(n).fill(0);
 function visit(i){if(i===n){fun(x);return;}for(let k=-R;k<=R;++k){x[i]=k;visit(i+1);}}
 visit(0);
}
function mat(n,s){
 const v=Array.from({length:n},(_,i)=>((s*s+7*i+11*i*i) % 13)-6);
 return v.map((x,i)=>v.map((y,j)=>x*y+(i===j?1+((s+i)%5):0)));
}
function quad(A,x){return A.reduce((a,row,i)=>a+x[i]*row.reduce((b,w,j)=>b+w*x[j],0),0);}
for(let n=1;n<=5;++n)for(let s=0;s<101;++s){
 const Q=mat(n,s);
 for(let j=0;j<31;++j){
   const x=Q.map((_,i)=>(i*i*3+j*(i+7)+s*s)%15-7),
         z=Q.map((_,i)=>(i*i*9+s*(i+5)+j*j)%17-8);
   const v=1+s%8,w=1+j%11,T=v+w;
   check(w*T*quad(Q,x)+v*T*quad(Q,z.map((a,i)=>a-x[i]))
     ===v*w*quad(Q,z)+quad(Q,x.map((a,i)=>T*a-v*z[i])),"exact completion of squares");
 }
}
for(let n=1;n<=4;++n)for(let s=0;s<81;++s){
 const Q=mat(n,s);let min=Infinity, S=[];
 const bound=Math.floor(Math.sqrt(Math.min(...Q.map((r,i)=>r[i]))));
 vectors(n,bound,x=>{const q=quad(Q,x);if(q>0&&q<=min){
   if(q<min){min=q;S=[];}S.push([...x]);
 }});
 check(S.length%2===0,"shortest generated shell has opposite pairs");
 for(const x of S)for(const y of S)if(x.every((a,i)=>(a-y[i])%2===0)){
   check(x.every((a,i)=>a===y[i])||x.every((a,i)=>a===-y[i]),"shortest shell parity multiplicity");
   const a=x.map((v,i)=>(v+y[i])/2),b=x.map((v,i)=>(v-y[i])/2);
   check(quad(Q,a)+quad(Q,b)===min,"exact parallelogram obstruction");
 }
}
const {exp,log,log1p,expm1,max,min,abs,sqrt,PI,cos}=Math;
const beta=2*PI*PI;
function gaussian(v){
 const m=Math.ceil(12*sqrt(v))+3, a=Array.from({length:2*m+1},(_,i)=>exp(-(i-m)*(i-m)/(2*v)));
 const z=a.reduce((s,x)=>s+x,0);return a.map(x=>x/z);
}
function entropy(p){return -p.reduce((s,x)=>s+(x?x*log(x):0),0);}
function conv(a,b){
 const r=Array(a.length+b.length-1).fill(0);
 for(let i=0;i<a.length;++i)for(let j=0;j<b.length;++j)r[i+j]+=a[i]*b[j];
 return r;
}
for(let i=0;i<41;++i)for(let j=i;j<44;++j){
 const v=.02+i*.022,w=.02+j*.022, a=gaussian(v),b=gaussian(w),p=conv(a,b);
 check(exp(2*entropy(a))+exp(2*entropy(b))>exp(2*entropy(p)),"direct Shannon reverse inequality",true);
}
function poisson(v) {
 let z=0, dz=0;
 for(let k=1;k<=8;++k){const r=2*exp(-beta*v*k*k);z+=r;dz-=beta*k*k*r;}
 return [log1p(z),dz/(1+z)];
}
function exmMinusX(x){
 if(abs(x)>.01)return expm1(x)-x;
 let term=x,n=1,s=0;while(n<16){term*=x/(++n);s+=term;}return s;
}
function delta(v){
 const [F,F1]=poisson(v);return v*(2*F+exmMinusX(2*(F+v*F1)));
}
function fkl(x){
 if(abs(x)>.001)return (1+x)*log1p(x)-x;
 let p=x*x,s=0;
 for(let n=2;n<=12;++n){s+=(n%2?-1:1)*p/(n*(n-1));p*=x;}return s;
}
for(const v of [.9,1,1.2,2,3.5,6,10])for(const d of [0,.01,.035,.07,.13,.22,.4,.8,1.5,2.5,7,19]){
 const w=v+d,T=v+w,u=v*w/T,a=v/T, q=gaussian(T), m=(q.length-1)/2;
 const B=q.map((_,i)=>{let sum=0;for(let k=1;k<=7;++k)sum+=2*exp(-beta*u*k*k)*cos(2*PI*k*a*(i-m));return sum;});
 const mu=B.reduce((s,b,i)=>s+b*q[i],0);
 const D=B.reduce((s,b,i)=>s+q[i]*fkl((b-mu)/(1+mu)),0);
 const gap=delta(v)+delta(w)-delta(T)+T*(-expm1(-2*D));
 const norm=4*v*exp(-beta*v);
 const pred=(1+exp(-beta*d/2))**2;
 // At these scales the analytic estimate for the variance-refitting correction
 // is already far smaller than this tolerance.
 check(abs(gap/norm-pred)<.2/v,"balanced-to-unbalanced coefficient "+[v,d,gap/norm,pred],true);
}
// Huge second widths: compute the cosine variance for the limiting continuous
// characteristic function with a cancellation-free formula. The Poisson images
// for these particular large T and tiny frequencies are exponentially suppressed.
for(const v of [1.5,3,6,12])for(const T of [1e4,1e8,1e16]){
 const a=v/T,u=v*(T-v)/T,kappa=beta*T*a*a;
 let variance=0;
 for(let i=1;i<=4;++i)for(let j=1;j<=4;++j){
   const cov=.5*exp(-kappa*(i-j)**2)*expm1(-2*kappa*i*j)**2;
   variance+=4*exp(-beta*u*(i*i+j*j))*cov;
 }
 const upper=10*exp(-2*beta*u)*min(1,beta**2*v**4/T**2);
 check(variance>0&&variance<upper,"cosine variance suppression at very large width disparity",true);
 check(T*variance/(4*v*exp(-beta*v))<1e-6,"negligible relative convolution defect",true);
}
console.log(JSON.stringify({exact,numerical}));

