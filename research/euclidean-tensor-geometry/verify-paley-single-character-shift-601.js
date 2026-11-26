// Exact single-character-shift improvement over every scalar Paley two-local dual at p=601.
// Node.js. The witness coefficients and all certificate checks are rational/integer.
'use strict';
const P=601,M=300,N=149,H=10,SHIFT=36;
const V1=[899,-167,526,-1148,277,37,-1479,-1315,398,-167,-167,-686,-1633,526,899,-497,-1479,-1479,343,-1793,-469,590,830,-497,-1012,19,-271,-469,830,899,119,-1012,-36,-225,-1315,277,19,-271,-1148,-497,398,398,-36,378,-1793,64,-469,378,343,590,-1633,-36,-225,37,-1265,277,-686,590,-271,19,-1793,-1148,-1633,343,119,526,830,119,-1315,-225,-686,-1012,37,378,-1265,378,37,-1012,-686,-225,-1315,119,830,526,119,343,-1633,-1148,-1793,19,-271,590,-686,277,-1265,37,-225,-36,-1633,590,343,378,-469,64,-1793,378,-36,398,398,-497,-1148,-271,19,277,-1315,-225,-36,-1012,119,899,830,-469,-271,19,-1012,-497,830,590,-469,-1793,343,-1479,-1479,-497,899,526,-1633,-686,-167,-167,398,-1315,-1479,37,277,-1148,526,-167,899];
const V2=[833,-186,495,-1208,270,31,-1479,-1320,397,-186,-186,-696,-1614,495,833,-519,-1479,-1479,278,-1834,-498,506,810,-519,-1003,-22,-299,-498,810,833,110,-1003,-41,-278,-1320,270,-22,-299,-1208,-519,397,397,-41,345,-1834,83,-498,345,278,506,-1614,-41,-278,31,-1267,270,-696,506,-299,-22,-1834,-1208,-1614,278,110,495,810,110,-1320,-278,-696,-1003,31,345,-1267,345,31,-1003,-696,-278,-1320,110,810,495,110,278,-1614,-1208,-1834,-22,-299,506,-696,270,-1267,31,-278,-41,-1614,506,278,345,-498,83,-1834,345,-41,397,397,-519,-1208,-299,-22,270,-1320,-278,-41,-1003,110,833,810,-498,-299,-22,-1003,-519,810,506,-498,-1834,278,-1479,-1479,-519,833,495,-1614,-696,-186,-186,397,-1320,-1479,31,270,-1208,495,-186,833];
function assert(ok,msg='assertion failed'){if(!ok)throw new Error(msg);}
const mod=(x,p=P)=>(x%p+p)%p, chi=new Int8Array(P).fill(-1);chi[0]=0;
for(let j=1;j<P;j++)chi[mod(j*j)]=1;
const Z=[1];for(let j=1;j<M;j++)Z.push(mod(H*Z[j-1]));
assert(new Set(Z).size===M&&Z.every(z=>chi[z]===1));
const F=Z.map(z=>chi[mod(1-z)]), f=(k)=>F[mod(k,M)];
const X=Array.from({length:N},(_,i)=>mod((Z[i+1]+2+Z[M-i-1])*451));
assert(new Set(X).size===N&&X.every(x=>chi[x]===1&&chi[mod(x-1)]===1));
const g400=(k)=>19*f(k)+15*(f(k+SHIFT)+f(k-SHIFT));
const A=Array.from({length:N},()=>Array(N).fill(0n));
const qs=[V1,V2].map(V=>[0n,0n,V.reduce((s,v)=>s+BigInt(v)*BigInt(v),0n)]);
assert(V1.length===N&&V2.length===N);
for(let i=0;i<N;i++)for(let j=0;j<N;j++){
 const u=j-i,v=i+j+2,c=i===j?1:chi[mod(X[i]-X[j])];
 if(i!==j)assert(c===f(u)*f(v));
 const d=i===j?0:(f(u)-f(v))*(g400(u)-g400(v));
 if(c===1)assert(d===0);
 // Integer matrix 400(96/5 I - B_g).
 A[i][j]=BigInt((i===j?7680:0)-400*c-d);
 for(let k=0;k<2;k++){
  const V=k===0?V1:V2, prod=BigInt(V[i])*BigInt(V[j]);
  qs[k][0]+=BigInt(c)*prod;
  if(c===-1)qs[k][1]+=4n*prod;
 }
}
const [[a,b,d],[e,f_s,g_s]]=qs;
assert(b<0n&&f_s>0n);
const nlo=a*f_s-e*b,dlo=d*f_s-g_s*b;
assert(dlo>0n&&2n*nlo>39n*dlo,'scalar lower bound is not above 39/2');
let prev=1n;
for(let i=0;i<N;i++)for(let j=i+1;j<N;j++)assert(A[i][j]===A[j][i]);
for(let k=0;k<N;k++){
 const a=A[k][k];assert(a>0n,'nonpositive pivot '+k);
 for(let i=k+1;i<N;i++)for(let j=i;j<N;j++){
  const d=A[i][j]*a-A[k][i]*A[k][j];
  assert(d%prev===0n);A[i][j]=d/prev;
 }
 prev=a;
}
console.log(JSON.stringify({p:P,shift:Z[SHIFT],witness:'19/400 f + 3/40 g_shift',strictUpper:'96/5',strictScalarLower:'39/2',lowerRational:[String(nlo),String(dlo)],positiveBareissPivots:N}));
