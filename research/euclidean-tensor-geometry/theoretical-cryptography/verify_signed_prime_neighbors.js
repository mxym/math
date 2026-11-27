"use strict";

// This checks small CRT laws only. There are no run-time inputs.
function gcd(a,b) { while(b) [a,b]=[b,a%b]; return a; }
function val(n,p,cap) {
  let v=0;
  while(v<cap && n%p===0) { n/=p; v++; }
  return v;
}
function abs(n) { return n<0n ? -n : n; }
let checks=0, atoms=0, crtCases=0, moduli=0;
function ok(x,msg) { checks++; if(!x) throw Error(msg); }
function law(p,cap) {
  const n=p**cap, count=Array.from({length:cap+1},()=>Array(cap+1).fill(0n));
  let total=0n;
  for(let u=1;u<n;u++) if(gcd(u,n)===1) {
    count[val(u-1,p,cap)][val(u+1,p,cap)]++; total++;
  }
  const a=count.map(row=>row.reduce((s,t)=>s+t,0n));
  const b=a.map((_,j)=>count.reduce((s,row)=>s+row[j],0n));
  const rows=[];
  let local=0n, support=0n;
  for(let i=0;i<=cap;i++) for(let j=0;j<=cap;j++) {
    if(!a[i] || !b[j])continue;
    const q=count[i][j]*total, jnt=a[i]*b[j];
    rows.push({q,jnt});
    local+=abs(q-jnt);
    if(q) support+=jnt;
  }
  const den=total*total;
  if(p>=5) ok(local*BigInt((p-1)**2)===4n*den,"single-prime distance");
  if(p===2||p===3) ok(support*2n===den,"half independent support");
  return {rows,total,den,support};
}
for(const primes of [[2,3],[2,3,5],[2,3,5,7],[2,3,5,7,11,13,17]]) {
  const laws=primes.map(p=>law(p,p<=7?3:1));
  let dp=0n, allowed=0n, bad=0n;
  function walk(i,q,j) {
    if(i===laws.length) {
      atoms++; dp+=abs(q-j);
      if(q) { ok(q>=j,"true law dominates on allowed support"); allowed+=j; }
      else bad+=j;
      return;
    }
    for(const row of laws[i].rows) walk(i+1,q*row.q,j*row.jnt);
  }
  walk(0,1n,1n);
  const den=laws.reduce((s,m)=>s*m.den,1n);
  let num=1n, denom=4n;
  for(const p of primes.filter(p=>p>=5)) {
    num*=BigInt((p-1)**2-1); denom*=BigInt((p-1)**2);
  }
  ok(allowed*denom===den*num,"Euler product of allowed support");
  ok(dp===2n*bad && allowed+bad===den,"exact total variation");
}

// Check the finite CRT mass for marked base classes and lifted bad events.
// Ranges force genuine lifting on both 2 and 3 as well as inactive events.
for(const r2 of [-1,1]) for(const r3 of [-1,1]) for(const h2 of [2,3])
for(const h3 of [1,2]) for(const mark5 of [-1,0,1]) for(let mask=0;mask<8;mask++) {
  const d=2**h2*3**h3*(mark5===0?1:5);
  const e=(mask&1?2:1)*(mask&2?3:1)*(mask&4?5:1), m=d*e;
  const mod=(x,k)=>(x%k+k)%k;
  let hits=0, units=0;
  for(let u=0;u<m;u++) if(gcd(u,m)===1) {
    units++;
    if(mod(u-r2,2**h2)||mod(u-r3,3**h3))continue;
    if(mark5!==0&&mod(u-mark5,5))continue;
    if((mask&1)&&mod(u-r2,2**(h2+1)))continue;
    if((mask&2)&&mod(u-r3,3**(h3+1)))continue;
    if(mask&4) {
      if(mark5!==0&&mod(u-mark5,25))continue;
      if(mark5===0&&mod(u-1,5)&&mod(u+1,5))continue;
    }
    hits++;
  }
  const phiD=2**(h2-1)*2*3**(h3-1)*(mark5===0?1:4);
  const den=phiD*(mask&1?2:1)*(mask&2?3:1)*
            (mask&4?(mark5===0?4:5):1);
  const num=(mask&4)&&mark5===0?2:1;
  ok(hits*den===units*num,"marked conditional sieve mass");
  crtCases++;
}

// For a prescribed exponent in m, count choices of e-membership,
// d-exponent and local sign / inactive residue.
const pset=[2,3,5,7,11];
function checkMultiplicity(i,n,k,w) {
  if(i===pset.length) {
    ok(n<=w,"bounded multiplicity of each modulus"); moduli++; return;
  }
  const p=pset[i];
  for(let h=0;h<=4;h++) {
    let ways=0;
    for(const e of [0,1]) {
      const d=h-e; if(d<0)continue;
      if(d===0&&p<=3)continue;
      if(d===1&&p===2)continue;
      ways+=d>0 || e===1?2:1;
    }
    checkMultiplicity(i+1,n*ways,k+(h>0?1:0),w*(h>0?4:1));
  }
}
checkMultiplicity(0,1,0,1);
console.log("OK: "+checks+" exact checks, "+atoms+" joint local atoms, "+
            crtCases+" marked CRT cases, "+moduli+" multiplicity profiles.");
