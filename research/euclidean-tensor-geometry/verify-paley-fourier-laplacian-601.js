// Exact nonscalar-vs-scalar two-local Paley dual separation at p=601.
// Node.js, no packages. All PSD and Rayleigh tests use BigInt.
'use strict';
const P=601, M=(P-1)/2, N=(P-5)/4, DEN=16, CUT_NUM=73, CUT_DEN=4;
const G=[0,1,-2,1,1,1,-1,2,-2,-2,3,0,-1,-2,2,0,0,0,1,0,-2,1,2,0,0,-1,1,-1,0,-1,-1,1,1,1,-1,1,1,2,-1,1,-1,2,-5,3,1,2,2,1,0,1,3,-1,0,-2,-2,-1,0,1,2,1,1,-1,-3,0,-1,0,-1,-1,-1,0,-1,0,4,0,2,2,1,-1,2,-1,0,1,-1,1,4,-1,1,0,-2,-1,-1,1,-1,-3,-2,-2,0,0,1,-1,1,-2,3,-3,1,0,-1,-2,0,-1,-1,0,-2,4,0,-2,0,0,-3,1,-1,-1,1,-2,-2,0,2,-2,0,-2,0,-1,-1,3,1,-1,2,-2,-1,1,0,2,2,0,-3,1,0,4,1,-2,-5]; // 16*g, on inverse-pair exponent representatives
const V=[-162,-2,-79,41,-31,-10,136,111,-34,-2,-2,48,162,-79,-149,25,136,136,-98,115,15,-133,-92,25,101,-45,-7,15,-92,-149,-20,101,-3,-37,111,-31,-45,-7,41,25,-34,-34,-3,-70,115,11,15,-70,-98,-133,162,-3,-37,-10,109,-31,48,-133,-7,-45,115,41,162,-98,-20,-79,-92,-20,111,-37,48,101,-10,-70,109,-70,-10,101,48,-37,111,-20,-92,-79,-20,-98,162,41,115,-45,-7,-133,48,-31,109,-10,-37,-3,162,-133,-98,-70,15,11,115,-70,-3,-34,-34,25,41,-7,-45,-31,111,-37,-3,101,-20,-149,-92,15,-7,-45,101,25,-92,-133,15,115,-98,136,136,25,-149,-79,162,48,-2,-2,-34,111,136,-10,-31,41,-79,-2,-149]; // Integer Rayleigh vector
function assert(ok,msg='assertion failed'){if(!ok)throw new Error(msg);}
const mod=(x,p=P)=>(x%p+p)%p, chi=new Int8Array(P).fill(-1); chi[0]=0;
for(let i=1;i<P;i++)chi[mod(i*i)]=1;
function multiplicativeOrder(h){
 let x=h,k=1;
 while(x!==1&&k<M){x=mod(x*h);k++;}
 return x===1?k:Infinity;
}
let h=2;while(h<P&&(chi[h]!==1||multiplicativeOrder(h)!==M))h++;
assert(h<P);
const Z=[1];for(let j=1;j<M;j++)Z.push(mod(h*Z[j-1]));
const inv4=(3*P+1)/4;
assert(Number.isInteger(inv4));
const X=Array.from({length:N},(_,i)=>mod((Z[i+1]+2+Z[M-i-1])*inv4));
assert(new Set(X).size===N&&X.every(x=>chi[x]===1&&chi[mod(x-1)]===1));
const F=Z.map(z=>chi[mod(1-z)]);
const rep=(j)=>Math.min(mod(j,M),mod(-j,M));
const g=(j)=>G[rep(j)];
assert(G.length===M/2+1&&V.length===N&&V.reduce((a,b)=>a+b,0)===0);
const A=Array.from({length:N},()=>Array(N).fill(0n));
let vd=0n,va=0n,vb=0n,wa=0n,wb=0n;
for(let i=0;i<N;i++){
 vd+=BigInt(V[i])*BigInt(V[i]);
 for(let j=0;j<N;j++){
  const u=mod(j-i,M),v=mod(i+j+2,M);
  const c=i===j?1:chi[mod(X[i]-X[j])];
  const d=i===j?0:(F[u]-F[v])*(g(u)-g(v));
  if(i!==j)assert(c===F[u]*F[v]);
  if(c===1)assert(d===0);
  const B16=DEN*c+d;
  A[i][j]=BigInt((i===j?CUT_NUM*DEN:0)-CUT_DEN*B16);
  const prod=BigInt(V[i])*BigInt(V[j]);
  va+=BigInt(c)*prod;wa+=BigInt(c);
  if(c===-1){vb+=4n*prod;wb+=4n;}
 }
}
for(let i=0;i<N;i++)for(let j=i+1;j<N;j++)assert(A[i][j]===A[j][i]);
// B_scalar(t) = I+C+4t*A_complement. Its two Rayleigh quotients
// are (wa+wb*t)/N and (va+vb*t)/vd. Their maximum is minimized
// at their intersection because wb>0 and vb<0.
assert(wb>0n&&vb<0n);
const lnum=va*wb-wa*vb, lden=vd*wb-BigInt(N)*vb;
assert(lden>0n&&BigInt(CUT_NUM)*lden<BigInt(CUT_DEN)*lnum,'scalar separation failed');
// Fraction-free symmetric elimination. Pivot k is the next leading
// principal determinant; all are positive, hence A is positive definite.
let prev=1n;
for(let k=0;k<N;k++){
 const a=A[k][k];
 assert(a>0n,'nonpositive pivot '+k);
 for(let i=k+1;i<N;i++)for(let j=i;j<N;j++){
  const b=A[i][j]*a-A[k][i]*A[k][j];
  assert(b%prev===0n,'inexact Bareiss division');
  A[i][j]=b/prev;
 }
 prev=a;
}
console.log(JSON.stringify({p:P,n:N,generator:h,positiveBareissPivots:N,threshold:'73/4',lowerScalarNumerator:String(lnum),lowerScalarDenominator:String(lden),scalarRayleigh:[[String(wa),String(wb),String(N)],[String(va),String(vb),String(vd)]]}));
