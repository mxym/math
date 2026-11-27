'use strict';
// Finite cyclotomic identities and toy log/spectral bounds. No external inputs.
let exact=0,numeric=0;
function check(ok,label){if(!ok)throw Error(label);exact++;}
function near(x,y,tol,label){if(!Number.isFinite(x)||!Number.isFinite(y)||Math.abs(x-y)>tol)throw Error(label+': '+x+' vs '+y);numeric++;}
function le(x,y,tol,label){if(!Number.isFinite(x)||!Number.isFinite(y)||x>y+tol)throw Error(label+': '+x+' > '+y);numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const gcd=(a,b)=>b?gcd(b,a%b):Math.abs(a);
const mod=(a,m)=>((a%m)+m)%m;
const units=m=>seq(m).filter(k=>gcd(k,m)===1);
const divs=m=>seq(m).map(i=>1+i).filter(d=>m%d===0);
const rad=m=>{let p=2,x=m,r=1;for(;p*p<=x;p++)if(x%p===0){r*=p;while(x%p===0)x/=p;}return x>1?r*x:r;};
const nz=(a)=>a.some(x=>x!==0n);
function trim(a){while(a.length>1&&a[a.length-1]===0n)a.pop();return a;}
function eq(a,b){return String(trim(a.slice()))===String(trim(b.slice()));}
function remainder(a,b){
 const r=a.slice(), n=b.length-1;
 for(let j=r.length-1;j>=n;j--){
   const v=r[j];if(v)for(let k=0;k<=n;k++)r[j-n+k]-=v*b[k];
 }
 return trim(r);
}
function quotient(a,b){
 const r=a.slice(), l=b.length-1, q=Array(Math.max(1,r.length-l)).fill(0n);
 for(let j=r.length-1;j>=l;j--){
  const v=r[j];q[j-l]=v;if(v)for(let k=0;k<=l;k++)r[j-l+k]-=v*b[k];
 }
 if(nz(r))throw Error('nonzero polynomial division remainder');
 return trim(q);
}
const mono=k=>Array(k).fill(0n).concat(1n);
const all=[null];
for(let m=1;m<=240;m++){
 let a=mono(m);a[0]=-1n;
 for(const d of divs(m))if(d<m)a=quotient(a,all[d]);
 all[m]=a;
 check(a.length-1===units(m).length,'Euler degree of cyclotomic polynomial');
 for(const r of divs(m)){
   const lower=all[m/r], n=lower.length-1, can=(m/r)%rad(m)===0;
   check(((a.length-1)===r*n)===can,'admissible block count');
   if(can){
     const b=Array(r*n+1).fill(0n);
     for(let j=0;j<=n;j++)b[r*j]=lower[j];
     check(eq(a,b),'relative cyclotomic power polynomial');
   }
 }
}
function add(a,b){
 const c=Array(Math.max(a.length,b.length)).fill(0n);
 for(let i=0;i<c.length;i++)c[i]=(a[i]||0n)+(b[i]||0n);
 return trim(c);
}
function scale(a,c){return trim(a.map(x=>x*c));}
function product(a,b,m){
 const c=Array(a.length+b.length-1).fill(0n);
 for(let i=0;i<a.length;i++)if(a[i])for(let j=0;j<b.length;j++)c[i+j]+=a[i]*b[j];
 return remainder(c,all[m]);
}
function pow(a,e,m){let b=[1n];for(let k=0;k<e;k++)b=product(a,b,m);return b;}
function root(k,m){return remainder(mono(mod(k,m)),all[m]);}
function trace(k,m){
 const a=Array(m).fill(0n);
 for(const j of units(m))a[mod(j*k,m)]++;
 const v=remainder(a,all[m]);
 check(v.length===1,'integer trace');
 return v[0];
}
for(const m of [4,8,9,12,16,18,20,24,27,32,36,40,45,48,54,63,72,80,90,96,108,120,144,180,216]){
 for(const r of divs(m/rad(m)))for(let k=0;k<m;k++){
  const wanted=k%r===0?BigInt(r)*trace(k/r,m/r):0n;
  check(trace(k,m)===wanted,'spherical relative trace blocks');
 }
}

// Exact Fourier zero criterion and finite correlation bound on generated fibers.
let seed=0x3119b2a2;
function gen(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
for(const m of [4,8,9,12,16,18,20,24,27,36,45,54,72,80,108,144]){
 for(const r of divs(m/rad(m)))if(r>1){
  const b=m/r, aK=units(m);
  for(const tau of units(b)){
   const f=aK.filter(k=>k%b===tau);
   check(f.length===r,'each fiber has the exact extension degree');
   for(let run=0;run<10;run++){
     const weighted=f.map((a,i)=>run===0?5:run===1?(i===0?3:1):1+gen(100));
     const equal=weighted.every(w=>w===weighted[0]);
     let vanishes=true,rho=0;
     const total=weighted.reduce((x,y)=>x+y,0);
     for(let k=1;k<r;k++){
        const coeff=Array(m).fill(0n);
        let re=0,im=0;
        for(let j=0;j<r;j++){
           const v=mod(f[j]*k,m),w=weighted[j];
           coeff[v]+=BigInt(w);
           re+=w*Math.cos(2*Math.PI*v/m);
           im+=w*Math.sin(2*Math.PI*v/m);
        }
        if(nz(remainder(coeff,all[m])))vanishes=false;
        rho=Math.max(rho,Math.hypot(re,im)/total);
     }
     check(vanishes===equal,'rational-arithmetic Fourier orthogonality');
     const Delta=Math.log(Math.max(...weighted)/Math.min(...weighted));
     le(Math.tanh(Delta/2)/(r-1),rho,2e-12,'explicit lower correlation bound');
     le(rho,Math.min(1,Math.expm1(Delta)),2e-12,'explicit upper correlation bound');
     if(r===2)near(rho,Math.tanh(Delta/2),2e-12,'two-element fiber sharp lower bound');
   }
  }
 }
}

function bareiss(M){
 const a=M.map(r=>r.slice()),n=a.length;let before=1n,sign=1n;
 for(let k=0;k+1<n;k++){
   if(a[k][k]===0n){
     let j=k+1;while(j<n&&a[j][k]===0n)j++;
     if(j===n)return 0n;
     [a[k],a[j]]=[a[j],a[k]];sign=-sign;
   }
   const p=a[k][k];
   for(let i=k+1;i<n;i++)for(let j=k+1;j<n;j++)a[i][j]=(a[i][j]*p-a[i][k]*a[k][j])/before;
   for(let i=k+1;i<n;i++)a[i][k]=0n;
   before=p;
 }
 return sign*a[n-1][n-1];
}
function norm(a,m){
 const n=all[m].length-1;
 const cs=seq(n).map(j=>product(a,root(j,m),m));
 return bareiss(seq(n).map(i=>cs.map(u=>u[i]||0n)));
}
function scalarDiv(a,d){
 check(a.every(x=>x%d===0n),'quotient is integral');
 return a.map(x=>x/d);
}
for(const [m,p] of [[4,2],[8,2],[16,2],[32,2],[9,3],[27,3],[25,5]]){
 const n=all[m].length-1;
 const pi=add([1n],scale(root(1,m),-1n));
 const g=quotient(add(all[m],[-BigInt(p)]),[-1n,1n]);
 check(eq(product(g,pi,m),[BigInt(p)]),'formal reciprocal of the ramified generator');
 check(norm(pi,m)===BigInt(p),'prime ideal norm');
 for(const r of divs(m/rad(m))){
   const y=add([1n],scale(root(r,m),-1n));
   check(norm(y,m)===BigInt(p)**BigInt(r),'relative ramification exponent from norm');
   const u=scalarDiv(product(y,pow(g,r,m),m),BigInt(p)**BigInt(r));
   const nu=norm(u,m);
   check(nu===1n||nu===-1n,'relative generator divided by the corresponding prime power is a unit');
 }
 if(p===2){
   const i=root(m/4,m), ib=root(-m/4,m),a=add([1n],i),conj=add([1n],ib);
   check(eq(product(a,conj,m),[2n]),'exceptional real-base balanced multiplier');
   check(norm(a,m)===2n**BigInt(n/2),'norm of exceptional generator');
   const u=scalarDiv(product(a,pow(g,n/2,m),m),2n**BigInt(n/2));
   const nu=norm(u,m);
   check(nu===1n||nu===-1n,'exceptional generator has exactly half the depth');
 }
}
// Abstract split incidence: quotient a cyclic set of finest blocks.
for(let D=1;D<=180;D++)for(const r of divs(D))for(const s of divs(D)){
 const h=r*s/gcd(r,s);
 for(let a=0;a<D;a++)check((a%r===0&&a%s===0)===(a%h===0),'intersection refines at lcm');
}
console.log({exact_checks:exact,numerical_checks:numeric});
