// Run: node check_cq_true_exterior_high_rank.js
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
function run(includeEight) {
let rows=[],m=zero,q=zero;
for(let r=includeEight?8:10;r<=24;r+=2){const n=r-1;
let mr=zero,qr=zero;
for(let g=(r===8?72:Math.floor(200/r));g<100;g++){
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
  for(const [j,coef,root] of [[4,96,a4],[6,3840,a6]]){
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
const mB=Q(includeEight?2380:514,1000000),qB=Q(includeEight?1459:777,1000000);
if(!lt(m,mB)||!lt(q,qB))throw Error("mass cert missed");
const J=Q(9072193375n,1000000000n),Ub=mul(Q(4651445,1000000),Q(123,105));
const unsigned=add(add(add(mul(Q(4),mB),mul(J,qB)),mul(mul(Q(12,5),Ub),mB)),mul(Q(2),mul(add(Q(63885,10000000),Q(111568,10000000)),mB)));
const target=includeEight?Q(995,10000):Q(4905,100000);
const rad=mul(mul(J,Q(3390)),qB);
const coeff=Q(6792,1000000);
const remaining=sub(target,unsigned);
if(!lt(zero,remaining)||!lt(mul(pow(coeff,2),rad),pow(remaining,2))) throw Error("canonical strict budget failed");
return {includeEight,rows,m:amb(m),q:amb(q),exactBudget:includeEight?'.0995':'.04905'};
}
for(const includeEight of [true,false]) console.log(JSON.stringify(run(includeEight)));
