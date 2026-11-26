// Exact small-path corroboration of the interval-extraction and inversion identities.
// Node.js, no packages. Integer coefficients are far below Number's exact range.
'use strict';
function requireEq(x,y,msg) {
  if (x.length!==y.length || x.some((v,i)=>v!==y[i])) throw new Error(msg);
}
function convolve(a,b) {
  const c=Array(a.length+b.length-1).fill(0);
  for (let i=0;i<a.length;++i) if (a[i])
    for (let j=0;j<b.length;++j) if (b[j]) c[i+j]+=a[i]*b[j];
  return c;
}
function run(w,a) {
  const n=w.length, W=[0], S=[0];
  for (let j=0;j<n;++j){W.push(W[j]+w[j]); S.push(S[j]+a[j]);}
  const N=W[n], M=S[n], z=S.map(s=>2*s-M);
  const byMass=()=>Array.from({length:N+1},()=>[0,0,0]);
  const direct=byMass(), sampled=byMass();
  function add(data,i,j,factor=1) {
    const m=W[j]-W[i], q=S[j]-S[i]; data[m][0]+=factor;data[m][1]+=factor*q;data[m][2]+=factor*q*q;
  }
  for (let i=0;i<n;++i) for (let j=i+1;j<=n;++j) add(direct,i,j);
  for (let i=1;i<n;++i) for (let j=i+1;j<n;++j) {
    add(sampled,0,i); add(sampled,i,j); add(sampled,j,n);
  }
  for (let r=1;r<n;++r) {
    const correction=2-(n-r);
    add(sampled,0,r,correction); add(sampled,n-r,n,correction);
  }
  add(sampled,0,n);
  for (let m=0;m<=N;++m) requireEq(sampled[m],direct[m],'wrong triple-cut correction');
  const B=Array(N+1).fill(0), A=[...B], C=[...B];
  for (let i=0;i<=n;++i){B[W[i]]=1; A[W[i]]=z[i]; C[W[i]]=z[i]**2;}
  const Br=[...B].reverse(), Ar=[...A].reverse().map(x=>-x), Cr=[...C].reverse();
  const bb=convolve(B,Br), ab=convolve(A,Br), ba=convolve(B,Ar);
  const cb=convolve(C,Br), bc=convolve(B,Cr), aa=convolve(A,Ar);
  for(let m=-N;m<=N;++m){
    const [count,sum,square]=sampled[Math.abs(m)];
    requireEq([bb[N+m],ab[N+m]+ba[N+m],cb[N+m]+bc[N+m]+2*aa[N+m]],
      [m===0?n+1:count, Math.sign(m)*2*sum, 4*square],'wrong reciprocal identity');
  }
  // The reconstructed numerator for A uses a previously chosen mass orientation.
  if (B.some((x,i)=>x!==Br[i])) {
    const sum=A.map((x,i)=>x+Ar[i]), bsum=convolve(B,sum), step=convolve(A,Br.map((x,i)=>x-B[i]));
    requireEq(step,ab.map((x,i)=>x+ba[i]-bsum[i]),'wrong asymmetric inversion');
    return false;
  }
  const csr=convolve(B,C.map((x,i)=>x+Cr[i]));
  requireEq(aa.map(x=>2*x),cb.map((x,i)=>x+bc[i]+2*aa[i]-csr[i]),'wrong symmetric inversion');
  return true;
}
let total=0,palindromic=0;
for(let n=2;n<=7;++n)for(let k=0;k<3**n;++k) {
  let q=k;const w=Array.from({length:n},()=>{const x=[2,3,7][q%3];q=Math.floor(q/3);return x;});
  const a=Array.from({length:n},(_,i)=>(13*i*i+3*k*i+7*k)%23-11);
  total++;palindromic+=Number(run(w,a));
}
console.log(JSON.stringify({total,palindromic,nonpalindromic:total-palindromic}));
