'use strict';
// Exact integer replay of necessary SRG parameters for minimum outdegree 11n/40.
// The parameter products outside traceSurvives fit in the safe integer range.
const limit=158202, fLimit=561, tLimit=41, survivors=[];
const least=new Uint32Array(limit+2);
for(let p=2;p<least.length;p++) if(!least[p]) {
 for(let j=p;j<least.length;j+=p) if(!least[j]) least[j]=p;
}
function divisorsUpTo(factors,high){
 const ex=new Map();
 for(let a of factors) while(a>1){const p=least[a];ex.set(p,1+(ex.get(p)||0));a/=p;}
 const ds=[1];
 for(const [p,e] of ex){
  const len=ds.length;
  let power=1;
  for(let j=1;j<=e;j++){
   power*=p;
   for(let i=0;i<len;i++) if(ds[i]*power<=high)ds.push(ds[i]*power);
  }
 }
 return ds;
}
function traceSurvives(n,k,L,r,t,d){
 const N=BigInt(n), K=BigInt(k), R=BigInt(r), S=-BigInt(t), D=BigInt(d), a=K-2n*D;
 let squares=0n,prev=0n;
 for(let i=1n;i<=N;i++){
  const T=[N*N*a,2n*N*(K-D)*i,((2n*(K-D)-S)*N-(K-S)*i)*i].reduce((a,b)=>a<b?a:b);
  squares+=(T-prev)**2n;prev=T;
 }
 const variance=squares-a*a*N**3n;
 const lhs=(BigInt(L)-3n*R)*K*K*N**3n;
 const rhs=3n*(BigInt(L)-R)*variance;
 return lhs<=rhs;
}
let preMajorization=0;
for(let t=2;t<=tLimit;t++) for(let r=1;r<=Math.floor(limit/t);r++){
 const k0=r*t, C=(r+1)*(t-1), M=k0*C;
 const den=limit-1-k0-C, high=limit-2-k0;
 if(den<=0||high<1)continue;
 const low=Math.ceil(M/den);
 if(low>high)continue;
 for(const mu of divisorsUpTo([r,t,r+1,t-1],high)){
  if(mu<low)continue;
  const k=k0+mu, ell=C+M/mu, n=1+k+ell, d=Math.floor((11*n+39)/40);
  if(n>limit||1000*r<21*n||k<2*d||n-2-2*k+mu<0)continue;
  if((r+1)*(k+r-2*r*t)>(k+r)*(t-1)**2)continue;
  const L=mu+r-t, f=((n-1)*t-k)/(r+t);
  const d1=Math.max(d,Math.floor(2000*(d-ell)/693)+1), a=k-2*d1;
  if(a<0||!Number.isInteger(f)||f<1||f>=n-1||f>fLimit||2*n>f*(f+3)||k*(L-3*r)>3*(L-r)*a)continue;
  preMajorization++;
  if(L<r||traceSurvives(n,k,L,r,t,d1))survivors.push([n,k,L,mu,r,-t,f]);
 }
}
survivors.sort((a,b)=>a[0]-b[0]);
const expected=[[10,6,3,4,1,-2,4],[16,10,6,6,2,-2,5],[27,16,10,8,4,-2,6]];
if(preMajorization!==62||JSON.stringify(survivors)!==JSON.stringify(expected))throw new Error(JSON.stringify({preMajorization,survivors}));
console.log({preMajorization,survivors});
