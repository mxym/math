"use strict";
// Finite clean-branch identities and explicitly illustrative Gaussian DFT checks.
let nExact=0,nFloat=0;
function eq(a,b,msg){nExact++;if(a!==b)throw Error(msg+": "+a+" != "+b);}
function approx(a,b,tol,msg){nFloat++;if(Math.abs(a-b)>tol)throw Error(msg+": "+a+" not near "+b);}
const sq=x=>x*x;
for(let m=2n;m<=20n;m++)for(let n=1n;n<m;n++){
  const u=sq(m)-sq(n),v=2n*m*n,w=sq(m)+sq(n); // sqrt(p)=u/w, sqrt(eps)=v/w
  const p=sq(u),q=sq(v),cross=u*v,den=sq(w),norm=sq(den);
  const a=[p,cross,q,-cross],b=[p,-cross,q,cross];
  const inner=a.map((x,j)=>x*b[j]).reduce((s,x)=>s+x,0n);
  eq(p+q,den,"unitary work columns");
  eq(a.map(sq).reduce((s,x)=>s+x,0n),norm,"auxiliary vector has unit norm");
  eq(inner,sq(p-q),"opposite auxiliary overlap");
  eq(norm-inner,4n*p*q,"two-point Fourier failure");
  eq((norm-inner)/2n,2n*p*q,"exact probability times common denominator");
}
for(let d=2n;d<=16n;d++)for(let i=0n;i<=d;i++)for(let j=0n;j<=d;j++){
  // Two equal initial probabilities and conditional failures i/d, j/d.
  const B=sq(d-i)+sq(d-j), V=sq(i)+sq(j), D=2n*sq(d);
  eq(D-B,2n*d*(i+j)-V,"junk mass from first/second moments");
}
const c=2**0.25;
function witness(N,R){
  const mid=(N-1)/2, h=1/Math.sqrt(N), L=Math.sqrt(N);
  const fs=Array.from({length:N},(_,i)=>{
    const x=(i-mid)*h;
    return Math.sqrt(h)*c*[-2,-1,0,1,2].reduce((s,k)=>s+Math.exp(-Math.PI*sq(x+k*L)),0);
  });
  const Z=Math.sqrt(fs.reduce((s,x)=>s+sq(x),0));
  const F=fs.map(x=>x/Z);
  const B=F.map((a,k)=>Math.abs((k-mid)*h)>=R?a:0);
  const delta=B.reduce((s,x)=>s+sq(x),0);
  const T=B.reduce((s,x)=>s+x,0)*Math.sqrt(h);
  let tv=0,probI=0,probJ=0;
  for(let j=-mid;j<=mid;j++){
    let G=0,H=0;
    for(let k=-mid;k<=mid;k++){
      const X=Math.cos(2*Math.PI*j*k/N);
      G+=X*F[k+mid];H+=X*B[k+mid];
    }
    G*=h;H*=h;
    approx(G,F[j+mid],3e-13,"self-Fourier periodized Gaussian");
    const p0=G*G,p1=sq(G-H)+sq(H);
    tv+=0.5*Math.abs(p1-p0);probI+=p0;probJ+=p1;
  }
  approx(probI,1,1e-12,"ideal law normalized");
  approx(probJ,1,1e-12,"flagged law normalized");
  if(tv>c*T+delta+1e-12 || !(tv>delta))
    throw Error("unexpected illustrative TV scale.");
  return {N,R,delta,tv,tvOverTailMass:tv/T};
}
console.log("OK: "+nExact+" exact finite identities.");
for(const R of [1.05,1.35,1.65])console.log(witness(513,R));
console.log("Illustrative floating checks total: "+nFloat);
