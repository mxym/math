// Run: node check_cq_independent_band_credit.js
// All proof decisions use exact BigInt and directed integer arithmetic.
// Decimal displays are not used for any branch or assertion.
"use strict";
// Part 1: independent actual positive shell.
(() => {

const S=100000000000000n,H=20000,P=1000,R=200;
const B=(x)=>BigInt(x);
const ce=(n,d)=>(n+d-1n)/d;
function ordinary(a){
  const A=H*a/P;
  if(!Number.isInteger(A))throw Error('noninteger H power floor');
  let l=S,u=S,L,Hh; // rank-one true harmonic is 1 at t=1
  for(let j=1;j*A<H;j++){
    const ll=[0n],hh=[0n];
    for(let i=0;i<H;i++){
      let c=0n,d=0n;
      if(i>=j*A){if(j===1){c=HBig*S/B(i+1);d=ce(HBig*S,B(i));}
        else {c=L[i-A]/B(i+1); d=ce(Hh[i+1-A],B(i));}}
      ll.push(ll[i]+c); hh.push(hh[i]+d);
    }
    if(j>1){l+=L[H-A]/HBig;u+=ce(Hh[H-A],HBig);}
    L=ll;Hh=hh;
  }
  return [l,u];
}
const HBig=B(H);
const PP=B(P),Den=PP**5n;
const psi=Array.from({length:P+1},(_,i)=>{let z=PP-2n*B(i);return 2n*z**3n*PP**2n-z**5n});
function cells(a,b){
 let v=Array(R+1).fill(0n);
 const inj=(score,w)=>{if(score<=0n)return;let i=Number((score*B(R)-1n)/Den);if(i<0||i>R)throw Error('threshold');v[i]+=w;};
 for(let i=a;i<Math.min(b,P/2);i++)inj(Den-psi[i],PP*S/B((i+1)*(P-i)));
 for(let i=a;i<Math.min(b,P/3+1);i++){
   for(let j=i+1;j<=Math.floor((P-i-3)/2);j++){
     const w=P-i-j;
     inj(Den-psi[i]-psi[j]-psi[w-2],PP*S/B((i+1)*(j+1)*w));
   }
 }
 for(let i=R-1;i>=0;i--)v[i]+=v[i+1];
 return v;
}
const b=123;
const [mbL,mbU]=ordinary(b),pBH=cells(b,P+1);

const QI=10000,DX=2*QI,AL=53577,AH=53578,BL=42664,BH=42665;
function drift(max){
 const rlo=Array(DX+1).fill(S),rhi=rlo.slice();
 for(let i=DX;i<max;i++){
   const l=rlo[i]-ce(BigInt(2*(i+1-DX))*rhi[i-DX],BigInt(i*i));
   const h=rhi[i]-BigInt(2*(i-DX))*rlo[i+1-DX]/BigInt((i+1)**2);
   rlo.push(l>0n?l:0n);rhi.push(h>0n?h:0n);
   if(rlo[i+1]>rhi[i+1])throw Error('Dickman enclosure');
 }
 const gl=[0n],gh=[0n];for(let j=0;j<max;j++){gl.push(gl[j]+BigInt(2*j+1)*rlo[j+1]);gh.push(gh[j]+BigInt(2*j+1)*rhi[j]);}
 const dl=Array(max+1).fill(0n),dh=dl.slice(),bl=dl.slice(),bh=dl.slice();
 for(let j=2;j<=AL;j++){
  const num=BigInt(j)*BigInt(j)*2n*BigInt(DX)**2n*S*S; const den=BigInt(QI)**2n;
  dl[j]=num/(den*gh[j]);dh[j]=ce(num,den*gl[j]);
 }
 dl[AH]=dl[AL];dh[AH]=ce(BigInt(AH)**2n*2n*BigInt(DX)**2n*S*S,BigInt(QI)**2n*gl[AL]);
 for(let j=BL;j<max;j++){
   const i=j-QI;
   bl[j+1]=bl[j]+(j<BH?0n:BigInt(2*j)*dl[i]/BigInt((i+1)**2));
   bh[j+1]=bh[j]+ce(BigInt(2*(j+1))*dh[i+1],BigInt(i*i));
   if(j>=AH){dl[j+1]=dl[j]+BigInt(2*j)*bl[i]/BigInt((i+1)**2); dh[j+1]=dh[j]+ce(BigInt(2*(j+1))*bh[i+1],BigInt(i*i));}
   if(dl[j+1]>dh[j+1]||bl[j+1]>bh[j+1])throw Error('DHR enclosure');
 }
 return [bl,dh];
}
function linear(max){
 let d=Array(max+1).fill(0n),b=d.slice();
 for(let j=0;j<=3*QI;j++)d[j]=2n*S;
 for(let j=2*QI;j<max;j++){
  const i=j-QI;
  b[j+1]=b[j]+ce(d[i+1],BigInt(i));
  if(j>=3*QI)d[j+1]=d[j]+ce(b[i+1],BigInt(i));
 }
 return d;
}
const [bl,dh]=drift(106000), d1=linear(53000);
function real(a){
 const n=Math.floor(999*QI/a), m=Math.floor(499*QI/a);
 return [[bl[n]*BigInt(QI*1000)**2n,S*BigInt(n*a)**2n],[d1[m]*BigInt(QI*1000),S*BigInt(m*a)]];
}
function testReal(a){
 const [maL,maU]=ordinary(a),pLB=cells(a,b);
 const [[Bn,Bd],[Un,Ud]]=real(a);
 const Cn=20881873n,Cd=1000000n,kn=44784588n,kd=10000000n;
 const norm=Bd*Ud*Cd*kd;
 const Am=Bn*Ud*Cd*kd-Cn*Bd*Ud*kd;
 const u=Un*Bd*Cd*kd, k=kn*Bd*Ud*Cd;
 if(u<=k)throw Error("banding sign");
 let s=0n;
 for(let i=1;i<=R;i++)for(let j=1;j<=R;j++){
   const bl=2n*(maU-mbL)-pLB[i]-pLB[j],bh=2n*mbU-pBH[i]-pBH[j];
   const z=Am*S-u*bl-(u-k)*bh;if(z>0n)s+=z;
 }
 const denom=norm*S*BigInt(R*R);
 return [s,denom];
}

const [credit,creditDen]=testReal(95);
if(credit*100000n<=5948n*creditDen)throw Error("actual positive band below .05948");
const [[Bn,Bd],[Un,Ud]]=real(95);
const show=(n,d)=>Number(n*10n**12n/d)/1e12;
console.log(JSON.stringify({positiveShell:show(credit,creditDen),DHRLow:show(Bn,Bd),roughHigh:show(Un,Ud)}));
})();

// Part 2: new rank-eight adverse sector, and only its incremental debit.
(() => {
const gcd=(a,b)=>{a=a<0n?-a:a; while(b){[a,b]=[b,a%b]}return a};
const Q=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);if(!d)throw Error("zero denominator");if(d<0n){n=-n;d=-d;}if(!n)return [0n,1n];const g=gcd(n,d);return [n/g,d/g]};
const add=([a,b],[c,d])=>Q(a*d+b*c,b*d);
const neg=([a,b])=>[-a,b]; const sub=(x,y)=>add(x,neg(y));
const mul=([a,b],[c,d])=>Q(a*c,b*d); const div=([a,b],[c,d])=>Q(a*d,b*c);
const lt=([a,b],[c,d])=>a*d<c*b;
const pow=([a,b],k)=>Q(a**BigInt(k),b**BigInt(k));
const max=(a,b)=>lt(a,b)?b:a, min=(a,b)=>lt(a,b)?a:b;
const amb=x=> Number(x[0]*10n**20n/x[1])/1e20;
const zero=Q(0),one=Q(1), A=Q(1,25);
const F=[1n];for(let i=1;i<=25;i++)F.push(F[i-1]*BigInt(i));
const choose=(n,h)=>F[n]/(F[n-h]*F[h]);
const a4=Q(2829,1000),a6=Q(3465,1000); 
if (!lt(Q(8),pow(a4,2))||!lt(Q(12),pow(a6,2)))throw Error("radical bounds");
function prmin(r,j,hi,s){
  let ans=null;
  for(let a=0;a<r;a++)for(let b=0;b<r-a;b++){
     const n=r-a-b;
     const t=div(sub(sub(s,mul(Q(a),A)),mul(Q(b),hi)),Q(n));
     if(lt(t,A)||lt(hi,t))continue;
     const h=Math.min(b,j),z=Math.min(n,j-h),l=j-h-z;
     const pr=mul(mul(pow(hi,h),pow(t,z)),pow(A,l));
     if(ans===null||lt(pr,ans))ans=pr;
  }
  if(ans===null||!lt(zero,ans))throw Error("no product vertex");
  return ans;
}
function runShape() {
let rows=[],m=zero,q=zero;
for(let r=8;r<=8;r+=2){const n=r-1;
let mr=zero,qr=zero;
for(let g=53;g<72;g++){
  const lo=max(Q(1,r),Q(g,200));
  const hi=min(Q(g+1,200),sub(one,mul(Q(n),A)));
  if(!lt(lo,hi))continue;
  let vol=zero;
  for(let h=0;h<=n;h++){
    const z=sub(sub(one,mul(Q(n),A)),mul(Q(h),sub(hi,A)));
    const v=sub(pow(max(zero,sub(z,lo)),n),pow(max(zero,sub(z,hi)),n));
    vol=add(vol,mul(Q((h%2?-1n:1n)*choose(n,h)),v));
  }
  if(lt(vol,zero))throw Error("negative volume");
  if(!lt(zero,vol))continue;
  vol=div(vol,Q(F[n]**2n));
  let density=zero, cap=zero;
  for(const [j,coef,root] of [[4,24,a4]]){
    const k=r-j;
    const scale=mul(Q(BigInt(coef)*(2n**BigInt(k-1))),root);
    const p=mul(lo,prmin(n,k-1,hi,sub(one,hi)));
    density=add(density,div(scale,mul(Q(j),mul(A,p))));
    const S=div(mul(Q(j),sub(one,lo)),Q(n));
    cap=add(cap,div(mul(scale,pow(S,j-1)),Q(BigInt(j)**BigInt(j))));
  }
  const mrbin=mul(vol,density);
  mr=add(mr,mrbin);qr=add(qr,mul(mrbin,cap));
}
m=add(m,mr);q=add(q,qr);rows.push({r,m:amb(mr),q:amb(qr)});
}


const mB=Q(1441,1000000),qB=Q(196,1000000),oldQ=Q(1459,1000000);
if(!lt(m,mB)||!lt(q,qB))throw Error("rank-eight shape mass caps");
const J=Q(9072193375n,1000000000n),Uh=mul(Q(4651445,1000000),Q(123,105));
const root1=Q(245519,100000),root2=Q(534757,1000000000);
if(!lt(mul(mul(J,Q(3390)),qB),pow(root1,2))||!lt(mul(qB,oldQ),pow(root2,2)))throw Error("directed square-root bounds");
const linear=add(add(add(mul(Q(4),mB),mul(J,qB)),mul(mul(Q(12,5),Uh),mB)),mul(Q(2),mul(add(Q(63885,10000000),Q(111568,10000000)),mB)));
const debit=add(add(linear,mul(Q(6792,1000000),root1)),mul(mul(Q(2),J),root2));
if(!lt(debit,Q(5282,100000)))throw Error("shape incremental cost >= .05282");
if (!lt(Q(66,10000),sub(Q(5948,100000),Q(5282,100000)))) throw Error("independent surplus <= .0066");
return {m:amb(m),q:amb(q),upperDebit:amb(debit)};
}
console.log(JSON.stringify(runShape()));

})();
