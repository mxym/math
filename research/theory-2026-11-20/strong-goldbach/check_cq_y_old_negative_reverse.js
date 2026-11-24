// Run: node check_cq_y_old_negative_reverse.js
// All branches and bounds are exact BigInt rationals. Display-only decimals
// may round tiny positive terms to zero; rational totals retain those terms.
"use strict";

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
function runOnly() {
let rows=[],m=zero,q=zero;
for(let r=8;r<=8;r+=2){const n=r-1;
let mr=zero,qr=zero;
for(let g=Math.floor(200/r);g<100;g++){
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
  for(const [j,coef,root] of [[4,96,a4]]){
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

if(!lt(m,Q(16,1000)))throw Error("rank 8 negative mass");
console.log(JSON.stringify({m8:amb(m),q8:amb(q)}));
}
runOnly();

const l=Q(4,100),h=Q(105,1000);
const rat=div(h,l),z=div(sub(rat,one),add(rat,one)),z2=pow(z,2);let k=z, log=zero;
for(let j=0;j<16;j++){log=add(log,div(k,Q(2*j+1)));k=mul(k,z2);}
log=mul(Q(2),add(log,div(k,mul(Q(33),sub(one,z2)))));
function integral(j){
   let ans=log;
   for(let n=1;n<=j;n++)ans=add(ans,mul(Q((n%2?-1n:1n)*choose(j,n),n),sub(pow(h,n),pow(l,n))));
   return ans;
}
const s2=Q(817,1000), s12=Q(3465,1000);
if(!lt(Q(2,3),pow(s2,2))||!lt(Q(12),pow(s12,2)))throw Error("radical caps");
const k6=add(div(mul(Q(3840),mul(s12,pow(div(sub(one,h),Q(5)),5))),one),mul(mul(Q(192),s2),pow(div(sub(one,h),Q(5)),2)));
if(!lt(Q(7),k6))throw Error("rank dominance");
const U6=mul(Q(3,5),add(mul(Q(3840,3125),mul(s12,integral(5))),mul(Q(192,25),mul(s2,integral(2)))));
const U8=mul(Q(3,5),mul(Q(768,49),mul(s2,integral(2))));
if(!lt(U6,Q(4909,1000))||!lt(U8,Q(6453,1000)))throw Error('rank receiver');
const uH=mul(Q(4651445,1000000),Q(123,105)),old=Q(840,10000),m8=Q(16,1000);
const aMax=Q(8472,100000), gm=Q(4367,1000000),a8=Q(1073,1000000000),gmTot=add(aMax,gm),uc=Q(314046,100000);
const rank5=mul(Q(2,3),sub(pow(Q(4,5),4),pow(Q(475,1000),4))),rank6=Q(2197,100000);
const gain=mul(Q(2),sub(mul(mul(Q(6,5),uH),add(rank5,rank6)),add(add(mul(U6,gmTot),mul(mul(Q(915,1000),uH),m8)),mul(U8,add(gm,a8)))));
const combined=mul(Q(2),add(add(mul(add(uc,U6),gmTot),mul(mul(Q(915,1000),uH),m8)),mul(U8,add(gm,a8))));
if(!lt(Q(2323,1000),gain)||!lt(combined,Q(1651,1000)))throw Error("actual reflow amount");
const ym=add(add(rank5,rank6),Q(92609478893615n,10n**15n)),amin=mul(Q(2,3),pow(Q(475,1000),4));
const burden=add(add(mul(Q(2),ym),pow(ym,2)),mul(mul(Q(2),ym),amin));
if(!lt(Q(8565,10000),burden)||!lt(Q(6885,10000),sub(mul(Q(2),ym),Q(189,10000))))throw Error("true dyadic barrier");
console.log(JSON.stringify({u6:amb(U6),u8:amb(U8),saved:amb(gain),totalOldNegativeOverlapNewUpper:amb(combined),dyadicDebitLower:amb(burden),ordinaryMassLower:amb(ym)}));
