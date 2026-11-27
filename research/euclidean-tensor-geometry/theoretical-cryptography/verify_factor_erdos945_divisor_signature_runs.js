"use strict";
// Exact small-instance check of the #945 prime-to-ell signatures and CRT.
let checks=0,instances=0;
const ok=(v,why)=>{++checks;if(!v)throw Error(why);};
const mod=(a,m)=>(a%m+m)%m;
const gcd=(a,b)=>b===0n?a:gcd(b,a%b);
const P=(n,k)=>{let g;while((g=gcd(n,k))>1n)n/=g;return n;};
const prime=(p)=>{if(p<2)return false;for(let d=2;d*d<=p;d++)if(p%d===0)return false;return true;};
const vp=(n,p)=>{let e=0;while(n%p===0n){n/=p;e++;}return e;};
const choose=(a,b)=>{let x=1n;for(let j=1;j<=b;j++)x=x*BigInt(a-j+1)/BigInt(j);return x;};
const dv=(n,k)=>{
  let z=1n;
  for(let p=2;p<=n;p++)if(prime(p)){
    let e=0;while(n%p===0){n/=p;e++;}
    z*=choose(e+k-1,k-1);
  }
  return z;
};
function inv(a,m){
  let s0=1n,s1=0n,r0=mod(a,m),r1=m;
  while(r1!==0n){const q=r0/r1;[r0,r1]=[r1,r0-q*r1];[s0,s1]=[s1,s0-q*s1];}
  ok(r0===1n,"distinct moduli are coprime");
  return mod(s0,m);
}
for(let D=2;D<=8;D++)for(let k=3;k<=24;k+=3){
  let r=0,b=1;
  while(b<k*D)b*=2,r++;
  const tags=[];
  for(let q=D+1;tags.length<r;q++)
    if(prime(q)&&(tags.length===0||q-tags.at(-1)>D))tags.push(q);
  const all=Array.from({length:b},(_,i)=>i);
  const masks=all.map(m=>tags.filter((q,j)=>(m>>j)&1));
  const used=Array.from({length:D+1},()=>new Set());
  const sig=Array.from({length:D+1},(_,ell)=>ell<2?[]:
     masks.map(xs=>P(xs.reduce((a,q)=>a*choose(q+ell-2,ell-1),1n),BigInt(ell))));
  for(let ell=2;ell<=D;ell++)ok(new Set(sig[ell]).size===b,"all masks are injective");
  const assigned=[];
  for(let i=1;i<=k;i++){
    let m=0,base=Array.from({length:D+1},(_,j)=>j>=2?P(dv(i,j),BigInt(j)):1n);
    function acceptable(j){for(let ell=2;ell<=D;ell++)if(used[ell].has(base[ell]*sig[ell][j]))return false;return true;}
    while(m<b&&!acceptable(m))m++;
    ok(m<b,"greedy excludes fewer than all masks");
    assigned.push(m);
    for(let ell=2;ell<=D;ell++)used[ell].add(base[ell]*sig[ell][m]);
  }
  let V=1n;
  for(let p=2;p<=k;p++)if(prime(p)){
    let w=BigInt(p);while(w<=BigInt(k))w*=BigInt(p);V*=w;
  }
  let n=0n,M=V,pp=k+1;const req=[];
  for(let i=1;i<=k;i++)for(const q of masks[assigned[i-1]]){
    while(!prime(pp))pp++;
    const p=BigInt(pp++),pw=p**BigInt(q);
    const residue=p**BigInt(q-1)-BigInt(i);
    n+=M*mod((residue-n)*inv(M,pw),pw);M*=pw;
    req.push({i,p,q});
  }
  ok(n>=0n&&n<M&&n%V===0n,"CRT representative");
  for(let i=1;i<=k;i++){
    const ni=n+BigInt(i);
    for(let p=2;p<=k;p++)if(prime(p))ok(vp(ni,BigInt(p))===vp(BigInt(i),BigInt(p)),"small-prime offset valuations");
    for(const {i:h,p,q} of req)ok(vp(ni,p)===(h===i?q-1:0),"exact tag valuation/no bleed");
  }
  for(let ell=2;ell<=D;ell++){
    ok(used[ell].size===k,"all positions separated for this ell");
    const el=BigInt(ell);
    for(let i=1;i<=k;i++){
      const v=dv(i,ell)*masks[assigned[i-1]].reduce((a,q)=>a*choose(q+ell-2,ell-1),1n);
      ok(P(v*el**BigInt(i%7),el)===P(v,el),"squarefree factors cannot change the signature");
    }
  }
  instances++;
}
console.log({checks,instances});
