"use strict";
// Fixed, tiny fixtures only. Exact integer/rational and cyclotomic checks;
// no claim about the quantitative analytic inequalities.
const assert = (ok, msg) => { if (!ok) throw Error(msg); };
const gcd = (a, b) => { while (b) [a,b] = [b,a%b]; return Math.abs(a); };
const mod = (n, d) => ((n%d)+d)%d;
const phi = d => Array.from({length:d},(_,v)=>v).filter(v=>gcd(v,d)===1).length;
const asPrimes = [];
for (let n=2;n<=96;n++) if (!asPrimes.some(p=>n%p===0)) asPrimes.push(n);
const mu = n => { let s=1; for(const p of asPrimes) if (n%p===0) {
  if (n%(p*p)===0) return 0; s=-s;
} return s; };
const ratGcd=(a,b)=>{while(b!==0n)[a,b]=[b,a%b];return a<0n?-a:a;};
const rat=(a,b)=>{a=BigInt(a);b=BigInt(b); const g=ratGcd(a,b);return [a/g,b/g];};
const add=([a,b],[c,d])=>rat(a*d+b*c,b*d);
const mul=([a,b],[c,d])=>rat(a*c,b*d);
const eq=([a,b],[c,d])=>a===c && b===d;
const zero=rat(0,1);
const D=49;
const divisors=d=>Array.from({length:d},(_,i)=>i+1).filter(i=>d%i===0);
const c=(d,t)=>divisors(gcd(d,Math.abs(t))).reduce((a,f)=>a+f*mu(d/f),0);
let numCDF=0, numPrefix=0, numGauss=0, numHarmonic=0, numHyper=0;
for(const [x,lo,hi] of [[10,0,1000],[19,450,1000],[23,690,1500],[31,0,4000]]) {
  const p=asPrimes.filter(n=>x<n&&n<=2*x), b=[];
  for(const r of p) for(const s of p) if(r<s&&lo<r*s&&r*s<=hi) b.push(r*s);
  const E=[null], Z=[null];
  for(let d=1;d<=D;d++) {
    const n=Array(d).fill(0);
    for(const v of b) n[v%d]++;
    const f=phi(d);
    E[d]=n.map((n,u)=>f*n-(gcd(u,d)===1?b.length:0));
    assert(E[d].reduce((u,v)=>u+v,0)===0,"zero average");
    Z[d]=Array.from({length:d},(_,u)=>
      rat(E[d].reduce((total,e,v)=> total+e*c(d,u-v),0),d*f));
    for(const q of divisors(d)) for(let u=0;u<q;u++) {
      const grouped=E[d].reduce((a,e,v)=>a+(v%q===u?e:0),0);
      assert(grouped*phi(q)===E[q][u]*f,"residue pushdown");
      numCDF++;
    }
  }
  for(let u=-35;u<=42;u++) {
    let left=zero;
    for(let t=1;t<=D;t++) {
      left=add(left,rat(E[t][mod(u,t)],phi(t)));
      let right=zero;
      for(let q=2;q<=t;q++) for(let k=1;q*k<=t;k++)
        right=add(right,mul(Z[q][mod(u,q)],rat(1,k)));
      assert(eq(left,right),"primitive-frequency recombination");
      numPrefix++;
    }
  }

  const w=4*x*x+60, tau=Array(w+1).fill(0);
  for(let d=1;d<=w;d++) for(let m=d;m<=w;m+=d) tau[m]++;
  for(let a=-32;a<=45;a++) {
    let low=0,high=0,actual=0,squares=0;
    for(const n of b) {
      const m=n+a, y=Math.floor(Math.sqrt(m));
      const l=Math.floor(Math.sqrt(Math.max(x*x,lo)+a)),
            h=Math.floor(Math.sqrt(Math.min(4*x*x,hi)+a));
      const small=t=>{let out=0;for(let d=1;d<=t;d++)if(m%d===0)out++;return out;};
      assert(2*small(y)-Number(y*y===m)===tau[m],"divisor hyperbola");
      low+=2*small(l);high+=2*small(h);actual+=tau[m];squares+=Number(y*y===m);
      numHyper++;
    }
    assert(low<=actual+squares&&actual+squares<=high,"two-cutoff bracket");
    numHyper++;
  }
}

// Polynomial arithmetic in Z[z] modulo the Nth cyclotomic polynomial.
function divideMonic(f, g) {
  f=f.slice(); const q=Array(Math.max(0,f.length-g.length+1)).fill(0);
  for(let j=q.length-1;j>=0;j--) {
    const a=f[j+g.length-1]; q[j]=a;
    for(let i=0;i<g.length;i++) {
      const product=a*g[i];
      assert(Number.isSafeInteger(product),"exact cyclotomic multiply");
      f[i+j]-=product;
      assert(Number.isSafeInteger(f[i+j]),"exact cyclotomic subtraction");
    }
  }
  return {q,r:f.slice(0,g.length-1)};
}
const phiPoly=new Map();
function cyclo(n) {
  if(phiPoly.has(n)) return phiPoly.get(n);
  let p=Array(n+1).fill(0);p[0]=-1;p[n]=1;
  for(const d of divisors(n)) if(d<n) {
    const {q,r}=divideMonic(p,cyclo(d));
    assert(r.every(v=>v===0),"cyclotomic exact division");p=q;
  }
  phiPoly.set(n,p);return p;
}
function makeExps(r,g,k,otherSign=null) {
  const map=new Map();let n=1;
  for(let i=0;i<k;i++){
    map.set(n,i);if(otherSign!==null) map.set(mod(-n,r),(i+otherSign)%k);
    n=n*g%r;
  }
  return map;
}
const fixtures=[
  [3,2,makeExps(3,2,2)],
  [4,2,makeExps(4,3,2)],
  [5,4,makeExps(5,2,4)],
  [8,2,new Map([[1,0],[3,1],[5,1],[7,0]])],
  [9,6,makeExps(9,2,6)],
  [12,2,new Map([[1,0],[5,1],[7,1],[11,0]])],
  [16,4,makeExps(16,3,4,0)],
];
for(const [r,k,C] of fixtures) {
  for(const s of divisors(r)) if(s<r)
    assert([...C].some(([u,i])=>[...C].some(([v,j])=>u%s===v%s&&i!==j)),
           "fixture has precise conductor");
  for(const [u,i] of C) for(const [v,j] of C)
    assert(C.get(u*v%r)===(i+j)%k,"fixture character");
  for(let q=r;q<=96;q+=r) {
    const N=q*k/gcd(q,k), p=cyclo(N), t=q/r;
    const positive=Array(N).fill(0);
    const support=[];
    for(let u=0;u<q;u++) if(gcd(u,q)===1) {
      const ind=(C.get(u%r)*(N/k)+u*(N/q))%N;
      positive[ind]++;support.push(ind);
    }
    if(q===r) {
      const f=Array(N).fill(0);f[0]=-r;
      for(const u of support)for(const v of support)f[mod(u-v,N)]++;
      assert(divideMonic(f,p).r.every(v=>v===0),"primitive Gauss square");
      numGauss++;
    }
    if(gcd(t,r)===1) for(const [u,i] of C) {
      const ind=((C.get(t%r)+i)*(N/k)+u*(N/r))%N;
      positive[ind]-=mu(t);
    }
    assert(divideMonic(positive,p).r.every(v=>v===0),"imprimitive Gauss identity");
    numGauss++;
  }
}
const Mh=64, hsum=[zero];
for(let i=1;i<=Mh;i++) hsum.push(add(hsum[i-1],rat(1,i)));
for(let h=1;h<=Mh;h++) for(let v=1;v<=Mh;v++) {
  let direct=zero, inverted=zero;
  for(let j=1;j<=v;j++)if(gcd(j,h)===1) direct=add(direct,rat(1,j));
  for(const d of divisors(h)) inverted=add(inverted,mul(rat(mu(d),d),hsum[Math.floor(v/d)]));
  assert(eq(direct,inverted),"harmonic unit inversion");
  numHarmonic++;
}
for(let n=1;n<=96;n++) {
  const g=divisors(n).reduce((a,f)=>add(a,rat(mu(f)**2,phi(f))),zero);
  assert(eq(rat(n,phi(n)),g),"totient convolution");
  numHarmonic++;
}
for(const p of asPrimes) {
  const a=rat(1,p*(p-1));
  assert(eq(mul(rat(1,p*p-p+1),add(rat(1,1),a)),a),"Euler log weight");
  numHarmonic++;
}
console.log({denominatorPushdown:numCDF, primitiveRecombination:numPrefix,
             gaussIdentities:numGauss, constantArithmetic:numHarmonic,
             hyperbola:numHyper,
             total:numCDF+numPrefix+numGauss+numHarmonic+numHyper});
