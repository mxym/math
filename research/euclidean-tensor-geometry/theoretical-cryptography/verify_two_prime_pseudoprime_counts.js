"use strict";

// Fixed small ranges; aggregate checks only, without listing passing inputs.
function gcd(a,b) { while(b) [a,b]=[b,a%b]; return a; }
function sieve(limit) {
  const keep=Array(limit+1).fill(true);
  keep[0]=keep[1]=false;
  for(let p=2;p*p<=limit;p++) if(keep[p])
    for(let j=p*p;j<=limit;j+=p) keep[j]=false;
  return keep.map((v,i)=>v?i:0).filter(Boolean);
}
function modPow(a,e,m) {
  a%=m;
  let y=1;
  while(e) { if(e%2) y=(y*a)%m; a=(a*a)%m; e=Math.floor(e/2); }
  return y;
}
const P=sieve(307);
let checks=0, pairs=0, passing=0, short=0, rootCases=0, crts=0;
function ok(x,msg) { checks++; if(!x) throw Error(msg); }

for(let a=2;a<=31;a++) {
  for(let i=0;i<P.length;i++) for(let j=i+1;j<P.length;j++) {
    const p=P[i], q=P[j], n=p*q, d=gcd(p-1,q-1);
    const lhs=modPow(a,n-1,n)===1;
    const rhs=modPow(a,d,n)===1;
    ok(lhs===rhs,"exact common-divisor equivalence");
    if(a===2) ok(lhs===(modPow(a,n,n)===a),"base-2 weak-congruence comparison");
    pairs++;
    if(lhs) {
      const A=BigInt(a)**BigInt(d);
      ok(A>BigInt(n) && (A-1n)%BigInt(n)===0n,"two primes divide the bin");
      passing++;
    }
    if(BigInt(a)**BigInt(q-p)<=BigInt((p-1)**2)) {
      ok(!lhs,"short window exclusion");
      short++;
    }
  }
  for(let d=1;d<=72;d++) for(const lo of [2,11,53,131]) {
    const admitted=P.filter(p=>p>=lo && (p-1)%d===0 && modPow(a,d,p)===1);
    const bucket=admitted.reduce((m,p)=>m*BigInt(p),1n);
    const A=BigInt(a)**BigInt(d);
    const low=Math.max(d+1,lo);
    ok((A-1n)%bucket===0n && BigInt(low)**BigInt(admitted.length)<A,
       "exact product bound underlying the logarithmic estimate");
  }
}
ok(passing>0 && short>0,"nonvacuous small and excluded cases");

for(let r=1;r<=36;r++) for(let s=r+1;s<=36;s++) {
  const bad=2*r*s*(s-r);
  for(const p of [2,3,5,7,11,13,17,19,23,29,31]) {
    let roots=0;
    for(let t=0;t<p;t++) if(((r*t+1)*(s*t+1))%p===0) roots++;
    ok(roots<=2 && (bad%p===0 || roots===2),"local root count");
    rootCases++;
  }
  for(const [p,q] of [[3,5],[5,7],[7,11]]) {
    if(bad%p===0 || bad%q===0)continue;
    const k=p*q;
    let roots=0, count=0;
    for(let t=0;t<k;t++) if(((r*t+1)*(s*t+1))%k===0)roots++;
    ok(roots===4,"CRT root count");
    for(let t=625;t<838;t++) if(((r*t+1)*(s*t+1))%k===0)count++;
    ok(Math.abs(count*k-213*4)<=4*k,"discrepancy of residue classes");
    crts++;
  }
}
console.log("OK: "+checks+" exact checks; "+pairs+" toy base-pairs, "+
            passing+" satisfying the congruence, "+short+
            " short-window exclusions, "+rootCases+" local cases, "+crts+" CRT cases.");
