// Exact rational certificates for the odd twisted t–J gap.
const D=1000000n;
const pAdd=(a,b,c=1n,d=1n)=>Array.from({length:Math.max(a.length,b.length)},(_,i)=>c*(a[i]??0n)+d*(b[i]??0n));
function pMul(a,b){let z=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)z[i+j]+=a[i]*b[j];return z;}
function shift(a){while(a.length>1&&!a.at(-1))a.pop();return a;}
function pCert(a,An,Bn,Dn){
 a=shift(a);let n=a.length-1,z=[a[n]],u=[1n],dp=1n;
 for(let j=n-1;j>=0;j--){
   z=pMul(z,[An,Bn]);u=pMul(u,[1n,1n]);dp*=Dn;
   const c=dp*a[j];if(c)for(let k=0;k<u.length;k++)z[k]+=c*u[k];
 }
 return z.every(x=>x>=0n)&&z.some(x=>x>0n);
}
const Q=10n**22n, PI0=31415926535897932384626n, PI1=PI0+1n; // PI0/Q < pi < PI1/Q
const ceilDiv=(a,b)=>a>=0n?(a+b-1n)/b:a/b;
const floorDiv=(a,b)=>a>=0n?a/b:-ceilDiv(-a,b);
function cosI(a,b){
 a=BigInt(a);b=BigInt(b);a=(a%(2n*b)+2n*b)%(2n*b);
 if(a>b)a=2n*b-a;
 const neg=2n*a>b;if(neg)a=b-a;
 if(!a)return neg?[-Q,-Q]:[Q,Q];
 if(2n*a===b)return [0n,0n];
 // Exact rational interval sums for cos(a*pi/b), a*pi/b in (0,pi/2).
 const p=PI0*a,r=PI1*a,s=Q*b;let lo=Q,hi=Q,fact=1n;
 for(let j=1;j<=13;j++){
   fact*=BigInt(2*j)*BigInt(2*j-1);
   const n=BigInt(2*j), denom=s**n*fact;
   const tl=floorDiv(Q*p**n,denom), th=ceilDiv(Q*r**n,denom);
   if(j%2){lo-=th;if(j<13)hi-=tl;}else{lo+=tl;hi+=th;}
 }
 return neg?[-hi,-lo]:[lo,hi];
}
const aUpper=(a,b)=>ceilDiv(2n*D*(Q-cosI(a,b)[0]),Q);
const aLower=(a,b)=>floorDiv(2n*D*(Q-cosI(a,b)[1]),Q);
const cosUp=(a,b)=>ceilDiv(D*cosI(a,b)[1],Q);
function checkPi(){
 const S=10n**36n;
 function atanI(q){
  let lo=0n,hi=0n;
  for(let j=0;j<=30;j++){
   const n=BigInt(2*j+1), den=n*q**n;
   if(j%2){lo-=ceilDiv(S,den);hi-=floorDiv(S,den);}
   else {if(j<30)lo+=floorDiv(S,den);hi+=ceilDiv(S,den);}
  }
  return [lo,hi];
 }
 const a=atanI(5n),b=atanI(239n),lo=16n*a[0]-4n*b[1],hi=16n*a[1]-4n*b[0];
 if(!(PI0*S<lo*Q && hi*Q<PI1*S))throw Error("π enclosure did not verify");
}
const G=[],ROT=new Map();
function gFill(L){
 if(!G.length)G.push([[1n]]);
 for(let n=G.length;n<=L;n++){
  let row=[[1n]];
  for(let k=1;k<n;k++)row.push(pAdd(G[n-1][k-1],[...Array(2*k).fill(0n),...G[n-1][k]]));
  row.push([1n]);G.push(row);
 }
}
function rotationPolys(L,k){
 let id=L+":"+k;if(ROT.has(id))return ROT.get(id);
 gFill(L);
 const M=[];
 for(let j=0;j<L;j++){
   let P=Array(2*k*(L-k)+1).fill(0n);
   for(let r=Math.max(0,k-(L-j));r<=Math.min(j,k);r++){
    const c=r*(L-j-k+r)+(k-r)*(j-r);
    const X=pMul(G[j][r],G[L-j][k-r]);for(let i=0;i<X.length;i++)P[i+c]+=X[i];
   }
   M.push(P);
 }
 ROT.set(id,M);return M;
}
function pNorm(L,k,r,den){
 const M=rotationPolys(L,k),Z=G[L][k],C=Array(2*k*(L-k)+1).fill(0n);
 for(let j=0;j<L;j++){
   const co=r===0?den:cosUp(2*r*j,L);
   for(let i=0;i<M[j].length;i++)C[i]+=co*M[j][i];
 }
 return [Z,C];
}
function even(N,k,j){
 const L=N-1,beta=aLower(1,L),c0=cosI(1,N),cb=cosI(L-2*j,N*L),cg=cosI(2*N-L+2*j,N*L);
 const B=ceilDiv(2n*D*(cb[1]-c0[0]),Q),C=floorDiv(2n*D*(c0[0]-cg[1]),Q);
 if(!(B>0n&&C>0n&&beta>B))throw Error("unstable even scaling");
 const [Z,Cr]=pNorm(L,k,j,D),A=[D,beta-2n*D,D];
 const P=pAdd(pMul(Z,pAdd(A,[0n,B],1n,-1n)),pMul(A,Cr),C*BigInt(L)*D,-(B+C)); 
 return pCert(P,0n,1n,1n);
}
function odd(N,k,num,den){
 const L=N-1,LL=BigInt(L),alpha=aUpper(1,N),beta=aLower(1,L),rho=aLower(2,L);
 if(!(alpha<beta&&alpha<rho&&D*(LL-1n)*(den-num)**2n < beta*LL*num*den && D*(LL-1n)*(den-num)**2n < rho*LL*num*den))throw Error("unstable odd scaling");
 const [Z,C]=pNorm(L,k,0,1n),E=pAdd(Z,C,LL,-1n),A=[D,beta-2n*D,D],B=[D*(LL-1n),-2n*D*(LL-1n),D*(LL-1n)];
 const P=pAdd(pMul(A,E),pMul(pAdd(A,[0n,rho-alpha]),Z),rho,-alpha*LL);
 const R=pAdd(pMul(pMul([0n,1n],A),E),pMul(Z,pMul(B,pAdd(pAdd(A,[0n,rho],LL,LL),B,1n,-1n))),rho*LL*LL,-LL);
 return pCert(P,0n,num,den)&&pCert(R,num,den,den);
}
function check(max){
 checkPi();let tests=0;
 function cut(N){
  const L=BigInt(N-1),a=aUpper(1,N),d=1000n;
  for(let j=1n;j<d;j++)if(D*(L-1n)*(d-j)**2n<=a*L*j*d)return j;
  throw Error("no split");
 }
 for(let N=5;N<=max;N+=2){
  const L=N-1;let count=0, bad=[];
  for(let k=2;k<=L/2;k++){
   if(k%2===0){for(let j=1;j<=L/2;j++){count++;if(!even(N,k,j))bad.push([k,j]);}}
   else {count++;if(!odd(N,k,cut(N),1000n))bad.push([k]);}
  }
  if(bad.length)throw Error(JSON.stringify({N,bad}));tests+=count;
 }
 return tests;
}
console.log(JSON.stringify({comparisonCertificates:check(41),largestOddN:41}));
