'use strict';
// Fixed generated algebraic examples. No external data, cryptosystem, or solver.
let exact=0, numeric=0;
function check(ok,label){ if(!ok) throw Error(label); exact++; }
function near(x,y,tol,label){ if(Math.abs(x-y)>tol) throw Error(label+': '+x+' vs '+y); numeric++; }
function visit(values,k,f,p=[]){
  if(!k) return f(p);
  for(const x of values) { p.push(x);visit(values,k-1,f,p);p.pop(); }
}
const seq=(n)=>Array.from({length:n},(_,i)=>i);
const sum=(x)=>x.reduce((a,b)=>a+b,0);

// A=J+J^{-1}, J a signed four-cycle coming from S^{n/4}.
for(const n of [4,8,16,32,64,128]){
  const h=n/4;
  const A=Array.from({length:n},()=>new Int8Array(n));
  for(let j=0;j<n;j++){
    const i=(j+h)%n, s=j+h>=n?-1:1;
    A[i][j]=s; A[j][i]=s;
  }
  for(let i=0;i<n;i++)for(let j=0;j<n;j++){
    check(A[i][j]===A[j][i] && (i!==j||A[i][j]===0),'symmetric hollow');
    let q=0;
    for(let k=0;k<n;k++)if(A[i][k])q+=A[i][k]*A[k][j];
    check(q===(i===j?2:0),'A squared');
    if(A[i][j])check(i%h===j%h,'signed cycle invariant');
  }
  for(const k of seq(n)){
    const shape=Math.sqrt(2)*Math.cos(Math.PI*(2*k+1)/4);
    near(Math.abs(shape),1,1e-12,'canonical two-level spectrum');
    near(shape,Math.sqrt(2)*Math.cos(Math.PI*(2*(n-1-k)+1)/4),1e-12,'paired spectrum');
  }
}

function q4(v){return sum(v.map(x=>x*x))-(v[0]*v[1]+v[1]*v[2]+v[2]*v[3]-v[3]*v[0]);}
function qc(v){return v[0]*v[1]+v[1]*v[2]+v[2]*v[3]-v[3]*v[0];}
function q2(v){return v[0]*v[0]+v[1]*v[1]-v[0]*v[1];}
const C4=new Int32Array(5), C2=new Int32Array(3);
visit(seq(11).map(i=>i-5),4,v=>{
 const l=sum(v.map(x=>x*x)), k=v.filter(Boolean).length, q=q4(v);
 check(7*q>=2*l && (q===0)===(l===0),'strict rational bound on four-cycle form');
 if(q===1){ C4[k]++; check(qc(v)===k-1 && l===k,'critical slopes'); }
});
visit(seq(13).map(i=>i-6),2,v=>{
 const l=sum(v.map(x=>x*x)), k=v.filter(Boolean).length, q=q2(v);
 check(2*q>=l,'rational half-bound');
 if(q===1){ C2[k]++; check(l===k,'dimer minimal support'); }
});
check(String(C4)==='0,8,8,8,0','four-cycle first shell');
check(String(C2)==='0,4,2','dimer first shell');

// Exact dyadic arithmetic for the connected-graph bound and Mayer coefficients.
// A pair has potential logarithm u, meaning exp(-V)=2^{-u}, or hard core.
const dy=(s,e=0)=>{s=BigInt(s);if(!s)return [0n,0];while(e>0 && (s&1n)===0n){s>>=1n;e--;}return [s,e];};
const add=([a,e],[b,f])=> e>=f?dy(a+(b<<BigInt(e-f)),e):dy((a<<BigInt(f-e))+b,f);
const neg=([a,e])=>[-a,e], mul=([a,e],[b,f])=>dy(a*b,e+f);
const pow2=(q)=>q>=0?dy(1n<<BigInt(q)):dy(1,-q);
const eq=(a,b)=>!add(a,neg(b))[0], le=(a,b)=>add(a,neg(b))[0]<=0n;
const abs=([a,e])=>[a<0n?-a:a,e];
const ONE=dy(1), ZERO=dy(0);
const pairData={};
function graphs(k){
 if(pairData[k])return pairData[k];
 const pairs=[];
 for(let j=0;j<k;j++)for(let i=0;i<j;i++)pairs.push([i,j]);
 const conn=[], tree=[];
 for(let mask=0;mask<1<<pairs.length;mask++){
   const root=seq(k), path=i=>root[i]===i?i:path(root[i]);
   const es=[];
   for(let j=0;j<pairs.length;j++)if(mask>>j&1){
     const [a,b]=pairs[j];root[path(a)]=path(b);es.push(j);
   }
   if(root.every((_,i)=>path(i)===path(0))){conn.push(es);if(es.length===k-1)tree.push(es);}
 }
 return pairData[k]={pairs,conn,tree};
}
function calc(tuple,R,bound){
 const {pairs,conn,tree}=graphs(tuple.length);
 const us=pairs.map(([i,j])=>{
   const [s,m]=tuple[i],[t,l]=tuple[j];
   return s===t?Infinity:R[s][t]*m*l;
 });
 const fs=us.map(u=>u===Infinity?dy(-1):add(pow2(-u),dy(-1)));
 const gs=us.map(u=>u===Infinity?ONE:add(ONE,neg(pow2(-Math.abs(u)))));
 let v=ZERO;
 for(const es of conn)v=add(v,es.reduce((d,e)=>mul(d,fs[e]),ONE));
 if(bound){
   let w=ZERO;
   for(const es of tree)w=add(w,es.reduce((d,e)=>mul(d,gs[e]),ONE));
   check(le(abs(v),mul(pow2(2*sum(tuple.map(p=>p[1]**2))),w)),'variable-stability connected bound');
 }
 return v;
}
let state=0x2dc8612d;
function gen(n){state=(Math.imul(1664525,state)+1013904223)>>>0;return (state>>>8)%n;}
for(let run=0;run<1200;run++){
 const R=Array.from({length:5},()=>Array(5).fill(0));
 for(let j=1;j<5;j++)for(let i=0;i<j;i++)R[i][j]=R[j][i]=gen(3)-1;
 const tuple=Array.from({length:2+gen(4)},()=>[gen(5),[-2,-1,1,2][gen(4)]]);
 calc(tuple,R,true);
}
const fac=(k)=>k===0?1:k*fac(k-1);
for(const R of [
 [[0,1,-1],[1,0,1],[-1,1,0]],
 [[0,-1,1],[-1,0,0],[1,0,0]],
 [[0,0,0],[0,0,0],[0,0,0]]
]){
 const A=[ONE,ZERO,ZERO,ZERO,ZERO], B=[ZERO,ZERO,ZERO,ZERO,ZERO];
 const states=[0,-1,1];
 visit(states,3,v=>{
   const k=v.filter(Boolean).length;
   if(!k)return;
   const expo=4*sum(v.map(m=>m*m))+R[0][1]*v[0]*v[1]+R[0][2]*v[0]*v[2]+R[1][2]*v[1]*v[2];
   A[k]=add(A[k],pow2(-expo));
 });
 const marks=seq(3).flatMap(i=>[[i,-1],[i,1]]);
 for(let k=1;k<=4;k++){
   visit(marks,k,tuple=>{
      B[k]=add(B[k],mul(pow2(-4*k),calc(tuple,R,false)));
   });
   let target=mul(dy(fac(k)),A[k]);
   for(let i=1;i<k;i++)target=add(target,neg(mul(dy(fac(k-1)/fac(i-1)),mul(B[i],A[k-i]))));
   check(eq(B[k],target),'exact Mayer coefficient vs formal logarithm');
 }
}

// Quantitative checks of block limits. Fixed-size enumeration only.
function mass4(beta,t){
 let v=0;
 visit(seq(9).map(i=>i-4),4,m=>{
   if(!m.some(Boolean))return;
   const q=q4(m)-(Math.SQRT2*beta-1)*qc(m);
   v+=Math.exp(-t*q);
 });
 return v;
}
for(const u of [-1,0,1]){
  for(const c of [-0.35,0,0.35]){
    const logn=400, n=Math.exp(logn), beta=1/Math.SQRT2+c/logn;
    const actual=(n/4)*Math.log1p(mass4(beta,logn+u));
    const limit=2*Math.exp(-u)*(1+Math.exp(Math.SQRT2*c)+Math.exp(2*Math.SQRT2*c));
    near(actual/limit,1,0.004,'four-cycle moving shape window');
  }
  const logn=300,n=Math.exp(logn);
  let dimer=0;
  visit(seq(7).map(i=>i-3),2,m=>{if(m.some(Boolean))dimer+=Math.exp(-(logn+u)*q2(m));});
  near((n/2)*Math.log1p(dimer),3*Math.exp(-u),1e-12,'dimer meeting window');
  // Shape with fixed half-gap, arbitrary fixed fugacity.
  const beta=0.3, z=1.8, n2=Math.exp(130), t2=130+u;
  let dilute=0;
  visit(seq(5).map(i=>i-2),4,m=>{
    const k=m.filter(Boolean).length;
    if(k)dilute+=Math.pow(z,k)*Math.exp(-t2*(q4(m)-(Math.SQRT2*beta-1)*qc(m)));
  });
  near((n2/4)*Math.log1p(dilute),2*Math.exp(-u)*z,1e-12,'uniform log formula on subfamily');
}
console.log({exact_checks:exact,numerical_checks:numeric});
