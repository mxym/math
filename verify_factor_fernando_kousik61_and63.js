// Exact finite-field cross-checks for the Fernando–Kousik Questions 6.1 and 6.3 note.
// Run as: node verify_factor_fernando_kousik61_and63.js
// The finite tests supplement, but do not replace, the proof.
"use strict";
const assert = require("node:assert/strict");
let checks = 0;
function eq(a,b) { ++checks; assert.equal(a,b); }
function ok(x) { ++checks; assert.ok(x); }

function field(d, modulus) {
  const N = 2**d;
  function multiply(a,b,P) {
    let c=0;
    while (b) {
      if (b&1) c^=a;
      b>>>=1;
      a<<=1;
      if (a&N) a^=P;
    }
    return c;
  }
  function degree(a) { return 31-Math.clz32(a); }
  function gcd(a,b) {
    while (b) {
      let r=a;
      while (r && degree(r)>=degree(b)) r^=b<<(degree(r)-degree(b));
      a=b; b=r;
    }
    return a;
  }
  function irreducible(P) {
    if (degree(P)!==d || !(P&1)) return false;
    let z=2;
    for (let j=1;j<=d;++j) {
      z=multiply(z,z,P);
      if (2*j<=d && gcd(z^2,P)!==1) return false;
    }
    return z===2;
  }
  if (modulus===undefined) {
    for (modulus=N+1; modulus<2*N && !irreducible(modulus); modulus+=2) {}
  }
  ok(irreducible(modulus));
  const mul=(a,b)=>multiply(a,b,modulus);
  function pow(a,k) {
    let b=1;
    while (k) {
      if (k%2) b=mul(b,a);
      k=Math.floor(k/2);
      a=mul(a,a);
    }
    return b;
  }
  const sq=a=>mul(a,a);
  const div=(a,b)=>{assert.ok(b); return mul(a,pow(b,N-2));};
  function trace(a,q,n) {
    let b=0;
    for (let j=0;j<n;++j) { b^=a; a=pow(a,q); }
    return b;
  }
  return {N,modulus,pow,mul,sq,div,trace};
}

function maps(s,e,modulus) {
  const q=2**s, m=e/2, F=field(s*e,modulus);
  const {pow,mul,trace}=F;
  const S=x=>trace(x,q,m);
  const sigma=x=>pow(x,q**m);
  const tau=x=>x^sigma(x);
  const T=S;
  const h1=u=>{const t=tau(u);return u^t^mul(t,pow(u,q-1));};
  const h3=u=>{const t=tau(u);return u^mul(t,pow(u^t,q-1));};
  const f1=x=>x^h1(S(x)), f3=x=>x^h3(S(x));
  const xi1=u=>u^S(h1(u)), xi3=u=>u^S(h3(u));
  return {...F,q,m,sigma,tau,S,T,h1,h3,f1,f3,xi1,xi3};
}

function definingPolynomialCheck(s,e) {
  const F=maps(s,e), {N,q,m,mul,pow,f1,f3}=F;
  const constants=Array.from({length:N},(_,a)=>a).filter(a=>pow(a,q)===a);
  eq(constants.length,q);
  // Factor the large n in the defining exponent into its three q-adic digits.
  for (let z=0;z<N;++z) {
    const y=pow(z,q)^z;
    let a1=0,a3=0;
    for (const a of constants) {
      const r=z^a, rm=pow(r,q**m), re=pow(r,q**e);
      a1^=mul(mul(pow(r,q-1),pow(rm,q-1)),re);
      a3^=mul(mul(r,pow(rm,q-1)),pow(re,q-1));
    }
    eq(a1,f1(y)); eq(a3,f3(y));
  }
}

function exhaustive(s,e,expected1,expected3) {
  const {N,f1,f3}=maps(s,e);
  const a=new Uint8Array(N),b=new Uint8Array(N);
  let ia=true,ib=true;
  for (let x=0;x<N;++x) {
    const r=f1(x),z=f3(x);
    if (a[r]) ia=false;
    if (b[z]) ib=false;
    a[r]=b[z]=1;
  }
  eq(ia,expected1);eq(ib,expected3);
}

function quarticTorus(s) {
  const {N,q,mul,pow,div,sigma,tau,xi1,xi3}=maps(s,4);
  let normal=0, zeros=0;
  for (let u=0;u<N;++u) {
    if (tau(u)!==1) continue;
    ++normal;
    const z=pow(u,q), w=z^u, Y=xi1(u), R=div(u,u^1);
    eq(pow(R,q*q+1),1);
    eq(Y,z^div(pow(w,2)^u,mul(u,z)));
    eq(Y,div(mul(u^1,pow(u,2*q)^u),mul(u,z)));
    eq(Y===0,pow(R,2*q-1)===1);
    eq(xi3(u),sigma(Y)^1);
    if (Y) eq(div(sigma(Y),Y),pow(R,q+2));
    else ++zeros;
  }
  eq(normal,q*q);
  eq(zeros,q%5===3?4:0);
}

function q4Pair(m) {
  const F=maps(2,2*m), {N,mul,div,pow,sq,S,T,tau,xi1,xi3}=F;
  const BbyAS=new Map();
  for (let b=0;b<N;++b)
    if (tau(b)===0) BbyAS.set(sq(b)^b,b);
  for (let U=0;U<N;++U) {
    if (tau(U)!==1) continue;
    const v=sq(U)^U, a=T(v), a2=sq(a), W=sq(v);
    eq(a^a2,1);
    eq(T(W),a2);
    const B=BbyAS.get(mul(a2,v));
    ok(B!==undefined);
    const z=U^B, Y1=xi1(U), U2=mul(a,z), Y2=xi1(U2), d=div(Y1^Y2,a2);
    eq(sq(z)^z,mul(a,v));
    eq(sq(d)^d,1);
    eq(d,U^mul(a2,B)^1^mul(a2,S(mul(v,U)))^T(mul(v,B)));
    for (const f of [xi1,xi3]) {
      const vals=[f(U),f(U^1),f(U2),f(U2^a)];
      eq(new Set(vals).size,4);
      eq(vals[0]^vals[1],a2);eq(vals[2]^vals[3],a2);
      for (const w of vals) eq(pow(w,4)^w,W);
    }
  }
}

function traceWitness(s,m) {
  const q=2**s, {N,trace,div}=field(s*m);
  let witness=0;
  for (let x=1;x<N;++x) {
    if (trace(x,2,s*m)===1 && trace(div(trace(x,2,s),x),q,m)===1) {
      witness=x;break;
    }
  }
  ok(witness);
  const D=q/2-1;
  ok(q**(m/2)>2*(q-1)*(D-1));
}

// The two-level Laurent coefficient certificate, over F4 = F2[c]/(c^2+c+1).
function momentCertificate(residue,j) {
  const F=field(2,7), {mul,pow}=F, J=j+2;
  const ad=(a,b)=>Array.from({length:Math.max(a.length,b.length)},
    (_,i)=>(a[i]||0)^(b[i]||0));
  function pm(a,b) {
    const r=Array(a.length+b.length-1).fill(0);
    for(let i=0;i<a.length;++i) for(let k=0;k<b.length;++k)
      r[i+k]^=mul(a[i],b[k]);
    return r;
  }
  const A=Array(9).fill(0); for(const i of [1,2,4,8])A[i]=1;
  const powers=[[1]];
  for(let i=1;i<2*J;++i) powers.push(pm(powers[i-1],A));
  const odd=(a,b)=>!(a&b);
  const inversePower=(c,p)=>pow(c, (3-(p%3))%3);
  function moment(k,c) {
    let answer=0;
    for(let n=0;n<k;++n)
      if(powers[n][k-1]) answer^=inversePower(c,n+1);
    return answer;
  }
  // [z^k](A(z)/z)^-1 is the moment on nonzero roots of A, for k>=1.
  const inv=[1];
  for(let k=1;k<=2*J;++k) {
    let a=0; for(const i of [1,3,7]) if(k>=i) a^=inv[k-i];
    inv.push(a);
  }
  const ba=(a,b)=>Array.from({length:Math.max(a.length,b.length)},
    (_,i)=>ad(a[i]||[0],b[i]||[0]));
  function bm(a,b) {
    const r=Array.from({length:a.length+b.length-1},()=>[0]);
    for(let i=0;i<a.length;++i) for(let k=0;k<b.length;++k)
      r[i+k]=ad(r[i+k],pm(a[i],b[k]));
    return r;
  }
  // Return N(V0+y) in F4[x][y] for w=a+x; V0 is either 0 or D=w^2+w+1.
  function numerator(a,shift,variable=true) {
    const w=variable?[a,1]:[a], w2=pm(w,w), w1=ad(w,[1]);
    const D=ad(ad(w2,w),[1]), V=[shift?D:[0],[1]];
    const M=ba(V,[w]), L=ba(V,[w2]), E=bm(V,ba(V,[D]));
    const Nt=bm(M,L), Nz=bm(M,ba(bm([w1],L),[w]));
    let N=ba(bm(Nt,Nt),bm(Nt,E));
    for(let j0=0;j0<j;++j0) N=bm(N,Nz);
    return N;
  }
  // res[k] = [x^-k] R_j(a+x) for 0<=k<=2J.
  function Laurent(a,c) {
    const res=Array(2*J+1).fill(0);
    for(let shift=0;shift<2;++shift) {
      const N=numerator(a,shift), C=a^(shift?(c^(residue%2)):mul(c,c));
      for(let k=1;k<=J;++k) for(let l=0;l<=J-k;++l) {
        const r=J-k-l, Dexp=J+r;
        if(!odd(J-1,r))continue;
        for(let n=0;n<k;++n) {
          if(!powers[n][k-1])continue;
          const Cexp=n+1, p=N[l]||[];
          for(let i=0;i<p.length;++i) {
            if(!p[i])continue;
            const base=Dexp+(C===0?Cexp:0)-i;
            for(let K=0;K<=base;++K) {
              const target=base-K;
              if(C===0) {
                if(odd(Dexp-1,target))res[K]^=p[i];
              } else {
                for(let g=0;g<=target;++g)
                  if(odd(Cexp-1,g)&&odd(Dexp-1,target-g))
                    res[K]^=mul(p[i],inversePower(C,Cexp+g));
              }
            }
          }
        }
      }
    }
    return res;
  }
  let total=0;
  const details=[];
  for(const c of [2,3]) {
    const cs=mul(c,c), L=Laurent(c,c), M=Laurent(cs,c);
    let part=0, special=0;
    if(residue===0||residue===2) {
      const ac=residue===0?0:1;
      for(let k=1;k<=2*J;++k)
        part^=mul(L[k]^M[k],moment(k,ac^c));
    } else {
      part^=L[0];
      for(let k=1;k<=2*J;++k)
        part^=mul(L[k],inv[k])^mul(M[k],moment(k,1));
      const N=numerator(c,0,false);
      for(let l=0;l<2*J;++l) special^=mul((N[l]||[])[0]||0,moment(2*J-l,1));
    }
    details.push({c,L,M,part,special,out:part^special});
    total^=part^special;
  }
  return {residue,j,total,details};
}
// Compute the obstruction a second way in the subfield F itself, using
// the trace and un-factored formulas. This is not used in the general proof.
function directMoment(s,j) {
  const q=2**s,{N,pow,mul}=field(2*s);
  const primes=[];
  let rem=N-1;
  for(let d=2;d*d<=rem;++d) if(rem%d===0) {
    primes.push(d);while(rem%d===0)rem/=d;
  }
  if(rem>1)primes.push(rem);
  let g=2;while(primes.some(p=>pow(g,(N-1)/p)===1))++g;
  const log=new Int32Array(N), ex=new Int32Array(2*(N-1));
  let a=1;for(let i=0;i<N-1;++i) {
    log[a]=i;ex[i]=ex[i+N-1]=a;a=mul(a,g);
  }
  eq(a,1);
  const M=(a,b)=>a&&b?ex[log[a]+log[b]]:0;
  const Q=(a,k)=>a?ex[(log[a]*k)%(N-1)]:0;
  const I=(a,b)=>a?ex[log[a]+N-1-log[b]]:0;
  let answer=0,count=0;
  for(let v=1;v<N;++v) {
    let a=v,w=0;
    for(let i=0;i<s;++i){w^=a;a=M(a,a);}
    if((Q(w,q)^w)!==1)continue;
    ++count;
    const R=I(w,v), vq=a;
    const b=1^R^I(w^1,vq);
    if(!b) throw Error("unexpected zero normalized trace");
    const t=I(1,b), Z=M(w^1^R,t);
    answer^=M(Q(Z,j),M(t,t)^t);
  }
  eq(count,N/2);
  return answer;
}

for (const [s,e] of [[2,2],[2,4],[3,2],[3,4]]) definingPolynomialCheck(s,e);
for (const [s,e,a,b] of [[2,2,false,false],[2,4,true,true],[2,6,false,false],
                         [2,8,true,true],[3,4,false,false],[4,4,true,false]])
  exhaustive(s,e,a,b);
for (const s of [2,3,4,5]) quarticTorus(s);
for (const m of [2,4]) q4Pair(m);
for (const s of [3,4,5,6]) traceWitness(s,4);
for (const [s,P,a,b,c] of [
  [4,65579,294,772,20873],
  [5,1048585,2330,2824,989541],
  [6,16777243,13959041,7330242,12566504],
]) {
  const {f3}=maps(s,4,P);
  ok(a!==b);
  eq(f3(a),f3(b));
  eq(f3(a),c);
}
const table=[
  [0,3,0,[3,0,0,2,0,3,2],[2,2,3,3,0,1,2],2],
  [1,5,2,[3,1,3,0,0,1,1],[0,2,1,1,2,2,1],3],
  [2,5,0,[3,2,3,0,0,2,1,3],[0,0,1,1,2,0,1,2],2],
];
for (const [r,j,L0,L,B,part] of table) {
  const a=momentCertificate(r,j), h=a.details[0], k=a.details[1];
  eq(a.total,1);eq(h.L[0],L0);eq(h.out,part);eq(h.special,0);
  const f4square=[0,1,3,2];
  const n=2*(j+2);
  for (let i=1;i<=n;++i) {
    eq(h.L[i],L[i-1]||0);eq(h.M[i],B[i-1]||0);
    eq(k.L[i],f4square[h.L[i]]);eq(k.M[i],f4square[h.M[i]]);
  }
  eq(k.M[0],f4square[h.M[0]]);eq(k.L[0],f4square[h.L[0]]);
  eq(k.out,f4square[h.out]);eq(k.special,0);
}
for(const [s,j] of [[4,3],[5,5],[6,5],[8,3],[9,5],[10,5]]) {
  ok(2*j<2**(s-1)-1);
  eq(directMoment(s,j),1);
}
console.log("Fernando–Kousik checks passed: "+checks);
