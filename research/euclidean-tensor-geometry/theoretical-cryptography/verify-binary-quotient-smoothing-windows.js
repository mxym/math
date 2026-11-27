"use strict";

// Deterministic generated binary vector spaces and mathematical formula checks.
let exact=0,numeric=0;
function chk(v,m){if(!v)throw new Error(m);++exact;}
function near(x,y,t,m){
  if(!Number.isFinite(x)||!Number.isFinite(y)||
     Math.abs(x-y)>t*Math.max(1,Math.abs(x),Math.abs(y))){
    throw new Error(m+": "+x+" vs "+y);
  }
  ++numeric;
}
function parity(z) {
  z^=z>>>16; z^=z>>>8; z^=z>>>4; return (0x6996>>>(z&15))&1;
}
function gm(n,r,M,b){
 let z=0;
 for(let i=0;i<n;i++)z|=parity((M>>>(i*r))&b)<<i;
 return z;
}
for (const [n,r] of [[1,1],[1,2],[2,1],[2,2],[2,3],[3,1],[3,2],[3,3]]) {
 const N=1<<n,B=1<<r,K=1<<(n*r);
 const E=Array.from({length:n},(_,i)=>BigInt(i+4)), O=E.map(x=>x-3n);
 const cntA=Array.from({length:B},()=>new Array(N).fill(0));
 const cntB=new Array(N).fill(0),jointS=Array.from({length:N},()=>new Array(N).fill(0));
 const jointP=Array.from({length:B},()=>Array.from({length:B},()=>new Array(N*N).fill(0)));
 for(let m=0;m<K;m++){
  const words=Array.from({length:B},(_,b)=>gm(n,r,m,b));
  const ker=new Array(N).fill(true);
  let r1=0n,r2=0n;
  for(let b=0;b<B;b++) {
    const z=words[b];let x=1n;
    for(let i=0;i<n;i++) x*=(E[i]+(((z>>i)&1)?-O[i]:O[i]));
    r1+=x;
    if(b!==0)cntA[b][z]++;
  }
  for(let b=1;b<B;b++)for(let c=1;c<b;c++)jointP[b][c][words[b]*N+words[c]]++;
  for(let z=0;z<N;z++) {
    ker[z]=words.every(w=>parity(w&z)===0);
    if(ker[z]) {
      let x=1n;for(let i=0;i<n;i++)x*=((z>>i)&1)?O[i]:E[i];
      r2+=x;if(z!==0)cntB[z]++;
    }
    for(let t=1;t<z;t++)if(ker[z]&&ker[t])jointS[z][t]++;
  }
  chk(r1===BigInt(B)*r2,"origin Fourier parity quotient");
 }
 for(let b=1;b<B;b++){
  for(const x of cntA[b])chk(x*N===K,"nonzero codeword uniform");
  for(let c=1;c<b;c++)for(const x of jointP[b][c])chk(x*N*N===K,"pairwise images");
 }
 for(let z=1;z<N;z++){
  chk(cntB[z]*B===K,"dual parity single constraint");
  for(let t=1;t<z;t++)chk(jointS[z][t]*B*B===K,"dual parity joint constraint");
 }
}
const pi=Math.PI;
function f(a,y) {
 let x=1;for(let k=1;k<=9;k++)x+=2*a**(k*k)*Math.cos(2*pi*k*y);return x;
}
function go(a,y) {
 let delta=0,q=0;
 for(let j=1;j<=10;j++){
   const v=2*a**(j*j)*Math.cos(2*pi*j*y);if(j%2)q+=v;else delta+=v;
 }
 return {p:1+delta,q,delta};
}
const info=(x)=>(1+x)/2*Math.log1p(x)+(1-x)/2*Math.log1p(-x);
const va=(x)=>(1-x*x)/4*(Math.log1p(x)-Math.log1p(-x))**2;
for(const a of [.008,.023,.048,.085,.14,.2,.31]){
 let mu=0,ga=0,be=0;
 const N=16384;
 for(let i=0;i<N;i++){
   const y=i/N,{p,q,delta}=go(a,y),r=q/p;
   if(i%23===0){
     near(f(a,y),p+q,6e-14,"even and odd decomposition");
     near(f(a,y+0.5),p-q,6e-14,"half shift sign");
   }
   mu+=info(r)/N;
   let t=-delta*delta/2,bias=t;
   for(let j=3;j<=9;j++){t*=-delta*(j-1)/j;bias+=t;}
   ga+=bias/N; // integral of delta itself is zero
   be+=Math.log1p(delta)**2/N;
 }
 near(mu/(a*a),1+a*a/2,12*a**4,"sign information expansion");
 near(ga/(a**8),-1,3*a**4+0.001,"even log mean");
 near((be-ga*ga)/(a**8),2,10*a**4+0.001,"even log variance");
}
for(let n=1;n<=8;n++)for(let u=1;u<=31;u++){
 const t=Array.from({length:n},(_,i)=>0.62*Math.sin((u+2)*0.7*(i+1))),
       m=t.reduce((a,b)=>a+info(b),0),v=t.reduce((a,b)=>a+va(b),0);
 let p0=0,p1=0,p2=0;
 for(let z=0;z<1<<n;z++){
   let w=1,s=0;
   for(let i=0;i<n;i++){
     const q=(((z>>i)&1)?-1:1)*t[i];w*=1+q;s+=Math.log1p(q);
   }
   p0+=w/2**n; p1+=w*s/2**n; p2+=w*s*s/2**n;
 }
 near(p0,1,1e-13,"posterior normalization");
 near(p1,m,1e-13,"posterior information mean");
 near(p2-p1*p1,v,1e-12,"posterior information variance");
}
function integr(f,a,b,N) {
 let q=0;const d=(b-a)/N;
 for(let i=0;i<=N;i++){
   const w=i===0||i===N?1:i%2===0?2:4;q+=w*f(a+i*d);
 }
 return d*q/3;
}
const phi=x=>Math.exp(-x*x/2)/Math.sqrt(2*pi);
const Phi=h=>h<=-11?0:h>=11?1:integr(phi,-11,h,4000);
for(const lambda of [0.02,.2,.6,1.6,4,9])for(const q of [.002,.12,.31,.74,.94,1]) {
 const u=Math.sqrt(2*lambda),h=(lambda-Math.log(q))/u;
 const ans=1-integr(z=>Math.min(1,q*Math.exp(-lambda+u*z))*phi(z),-11,11,20000);
 near(ans,Phi(h)-q*Phi(h-u),2e-7,"combined bounded-overlap profile");
}
console.log(exact+" exact finite-algebra checks; "+numeric+
            " deterministic numerical checks: PASS");
