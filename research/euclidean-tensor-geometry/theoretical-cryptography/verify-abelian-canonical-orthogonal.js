"use strict";
// Exact replay of the odd-conductor metric formula on generated finite character groups.
let exact=0;
function check(ok,msg){if(!ok)throw new Error(msg);++exact;}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a;}
function mod(a,n){const b=a%n;return b<0?b+n:b;}
function det(M){
 const n=M.length,A=M.map(r=>r.map(BigInt));let sign=1n,p=1n;
 for(let k=0;k<n-1;++k){
   let i=k;while(i<n&&A[i][k]===0n)++i;if(i===n)return 0n;
   if(i!==k){[A[i],A[k]]=[A[k],A[i]];sign=-sign;}
   for(let i=k+1;i<n;++i)for(let j=k+1;j<n;++j)A[i][j]=(A[i][j]*A[k][k]-A[i][k]*A[k][j])/p;
   p=A[k][k];for(let i=k+1;i<n;++i)A[i][k]=0n;
 }
 return sign*A[n-1][n-1];
}
const generators=new Map([[3,2],[5,2],[7,3],[17,3]]);
function build(r,kind,primes,seed,replayDirect){
 const noncyclic=kind==="noncyclic", n0=2**r, n=noncyclic?2*n0:n0;
 const A=4*n0,N=A/2;
 const sa=g=>Math.floor(g/n0),eu=g=>g%n0;
 function plus(g,h){return (sa(g)^sa(h))*n0+(g+h)%n0;}
 function mult(g,k){return (sa(g)*(k&1))*n0+mod(eu(g)*k,n0);}
 const neg=g=>mult(g,-1);
 const R=Array.from({length:n},(_,i)=>i);
 const units=new Map(), repres=Array(n).fill(-1);
 for(let s=0;s<2;++s){
   let u=1;
   for(let j=0;j<n0;++j){
     const v=s?A-u:u;
     const g=noncyclic?s*n0+j
       :kind==="sign"?s:(j+(kind==="mixed"?s*n0/2:0))%n0;
     units.set(v,g);if(repres[g]<0)repres[g]=v;
     u=5*u%A;
   }
 }
 check(units.size===N&&repres.every(u=>u>0),"dyadic quotient");
 const kernelD=[...units].filter(([_,g])=>g===0).map(([u])=>u);
 function act(u,i){const a=(u*i)%A;return a<N?[a,1]:[a-N,-1];}
 const B=[],used=new Set();
 for(let i=0;i<N;++i)if(!used.has(i)){
   const signs=new Map();let allowed=true;
   for(const a of kernelD){
     const [j,s]=act(a,i);used.add(j);
     if(signs.has(j)&&signs.get(j)!==s)allowed=false;
     signs.set(j,s);
   }
   if(allowed)B.push([...signs]);
 }
 check(B.length===n,"signed permutation fixed-basis rank");
 const sq=B.map(v=>n*v.length);
 function translate(g,v){return v.map(([i,w])=>{const [j,s]=act(repres[g],i);return [j,w*s];});}
 function pairing(g,x,y){
   const a=new Map(translate(g,x));return n*y.reduce((s,[i,w])=>s+w*(a.get(i)||0),0);
 }
 for(let i=0;i<n;++i)for(let j=0;j<n;++j)check(pairing(0,B[i],B[j])===(i===j?sq[i]:0),"orthogonal dyadic fixed basis");

 const odd=primes.reduce((a,b)=>a*b,1), q=[];
 let U=[[0,0]];
 for(let s=0;s<primes.length;++s){
   const p=primes[s],choices=R.filter(h=>mult(h,p-1)===0), im=choices[(seed*seed+seed*(s+3)+s+2)%choices.length];
   q.push(im);
   const J=[];let u=1;
   for(let j=0;j<p-1;++j){J.push([u,mult(im,j)]);u=u*generators.get(p)%p;}
   check(new Set(J.map(([u])=>u)).size===p-1,"generated odd unit labels");
   let a=odd/p,f=1;while((a*f)%p!==1)++f;a*=f;
   U=U.flatMap(([w,g])=>J.map(([u,h])=>[(w+u*a)%odd,plus(g,h)]));
 }
 const periods=new Map();
 for(const [u,g] of U){if(!periods.has(g))periods.set(g,[]);periods.get(g).push(u);}
 if(odd===1)periods.set(0,[0]);
 const H=[...periods.keys()],kT=periods.get(0).length;
 function cOdd(x){return primes.reduce((a,p)=>a*(x%p===0?p-1:-1),1);}
 function cDyad(x){return x%N===0?(x%A===0?N:-N):0;}
 const rv=new Map();
 for(const h of H){
   let s=0;
   for(const a of periods.get(0))for(const b of periods.get(h))s+=cOdd(a-b);
   check(s%kT===0,"odd period trace integral");rv.set(h,s/kT);
 }
 for(const h of H)check(rv.get(h)===rv.get(neg(h)),"period covariance symmetry");
 function gram(i,j){return H.reduce((s,h)=>s+rv.get(h)*pairing(h,B[i],B[j]),0);}
 function conductor(s,a) {
   let result=1;
   for(let j=0;j<q.length;++j){
     const v=q[j], val=mod(a*eu(v)+(noncyclic?s*sa(v)*n0/2:0),n0);
     if(val!==0)result*=primes[j];
   }
   return result;
 }
 const C=B.map((_,i)=>B.map((_,j)=>gram(i,j)));
 let product=sq.reduce((a,b)=>a*BigInt(b),1n);
 for(let s=0;s<(noncyclic?2:1);++s)for(let a=0;a<n0;++a)product*=BigInt(conductor(s,a));
 check(det(C)===product,"exact determinant equals conductor eigenvalue product");
 const hasI=H.every(h=>sa(h)===0);
 let off=false;
 for(let i=0;i<n;++i)for(let j=0;j<n;++j){
   check(C[i][j]===C[j][i],"symmetric twisted metric");
   if(i!==j&&C[i][j]!==0)off=true;
   if(noncyclic){
     const x=B[i][0][0],y=B[j][0][0];
     let expected=0;
     if(x===0)expected=i===j?n:0;
     else if(x===n/2)expected=i===j?n*conductor(1,0):0;
     else {
       const rootOrder=A/gcd(A,x), h=n0/(rootOrder/4);
       const p=conductor(0,h),q=conductor(1,h), [z,s]=act(A-1,x);
       expected=n*((x===y?(p+q)/2:0)+(z===y?s*(p-q)/2:0));
     }
     check(C[i][j]===expected,"exact Gram block prediction");
   }
 }
 check(off===(noncyclic&&!hasI),"complete diagonal criterion on generated twist");
 if(replayDirect){
   // Lift the basis into the full coprime cyclotomic product, then take its ambient
   // trace using the two independent Ramanujan sums. This bypasses (2).
   const vectors=B.map(b=>H.flatMap(h=>translate(neg(h),b).flatMap(([x,s])=>periods.get(h).map(y=>[x,y,s]))));
   const idx=kernelD.length*kT*H.length;
   for(let i=0;i<n;++i)for(let j=0;j<n;++j){
     let s=0;
     for(const [a,b,u] of vectors[i])for(const [c,d,v] of vectors[j])s+=u*v*cDyad(a-c)*cOdd(b-d);
     check(s===idx*C[i][j],"direct expanded trace of invariant basis");
   }
 }
}
for(let r=1;r<=4;++r)for(const kind of ["cyclic","mixed","noncyclic"])
 for(let s=0;s<25;++s)build(r,kind,s%2?[3,5,17]:[3,5,7],s,false);
for(let s=0;s<12;++s){
 build(1,"sign",s%2?[3,5]:[7],s,true);
 build(1,"noncyclic",[3,5],s,true);
 build(2,"mixed",[3,5],s,true);
}
console.log(JSON.stringify({exact}));

