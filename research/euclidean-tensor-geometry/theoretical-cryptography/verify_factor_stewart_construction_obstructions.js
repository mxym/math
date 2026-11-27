'use strict';
// Exact finite checks for FactorStewartConstructionObstructions.md.
let checks = 0;
function check(ok, why) { if (!ok) throw Error(why); ++checks; }
const abs = a => a < 0n ? -a : a;
function gcd(a, b) { a = abs(a); b = abs(b); while (b) [a,b] = [b,a%b]; return a; }
function R(n,d=1n) { if (d<0n) [n,d]=[-n,-d]; const g=gcd(n,d); return [n/g,d/g]; }
const add = (a,b) => R(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const neg = a => [-a[0],a[1]];
const sub = (a,b) => add(a,neg(b));
const mul = (a,b) => R(a[0]*b[0],a[1]*b[1]);
const div = (a,b) => mul(a,R(b[1],b[0]));
const pw = (a,b) => R(a[0]**BigInt(b),a[1]**BigInt(b));
const same = (a,b) => a[0]===b[0] && a[1]===b[1];
for (let u=1n;u<=85n;++u) for (let d=1n;d<=22n;++d) {
  if (gcd(u,d)!==1n) continue;
  const s=R(u,d);
  for (let U=1n;U<=120n;++U) {
    const t=sub(R(U),pw(s,3));
    if (!t[0]) continue;
    const z=div(pw(t,2),s);
    const V=add(pw(s,5),add(mul(R(5n,3n),mul(t,pw(s,2))),mul(R(5n,9n),z)));
    const val=div(add(neg(pw(s,5)),add(mul(R(5n*U),pw(s,2)),div(R(5n*U*U),s))),R(9n));
    check(same(V,val),'elimination identity');
    if (d!==1n) check(V[1]!==1n,'denominator forced out by unique lowest valuation');
    else {
      const h=mul(R(5n,9n),z);
      check((V[1]===1n)===(t[0]%3n===0n && h[1]===1n),'exact integral scale lattice');
    }
  }
}
for (let n=1n;n<=22000n;++n) for (const a of [n,-n]) {
  const s=5n*a*a,t=3n*a,U=s**3n+t,V=s**5n+5n*a*s*s+1n;
  const w=R(t,s**3n);
  const poly=add(R(135n),add(mul(R(405n),w),add(mul(R(396n),pw(w,2)),mul(R(125n),pw(w,3)))));
  check(poly[0]>0n,'positive residual factor');
  const gap=V**3n-U**5n;
  check(same(R(gap),mul(R(s**15n,729n),mul(pw(w,3),poly))),'exact gap factorization');
  check(gap===78125n*a**15n+5625n*a**10n+132n*a**5n+1n,'two-sign pair identity');
  check(gap*gap<=U**5n,'pair lies within a square-root span');
  if (n>=2n) check((5n*gap*gap<=U**5n)===(a<0n),'endpoint signs at finite checked parameters');
}

function trim(a){while(a.length && !a[a.length-1])a.pop();return a;}
function conv(a,b){if(!a.length||!b.length)return [];const c=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]+=a[i]*b[j];return trim(c);}
function plus(a,b,s=1n){return trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||0n)+s*(b[i]||0n)));}
function power(a,p){let res=[1n];for(let i=0;i<p;i++)res=conv(res,a);return res;}
function derivative(a){return trim(a.slice(1).map((a,i)=>a*BigInt(i+1)));}
function sc(a,n){return a.map(x=>x*BigInt(n));}
let seed=1419521;
function rand(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;}
for (let p=2;p<=8;p++) for(let q=2;q<=10;q++) for(let l=1;l<=3;l++) for(let i=0;i<15;i++){
  const m=q*l,n=p*l,D=p*m;
  const poly=r=>[...Array.from({length:r},()=>BigInt(rand()%7)-3n),1n];
  const A=poly(m),B=poly(n),C=plus(power(A,p),power(B,q),-1n),d=C.length-1;
  const W=plus(sc(conv(derivative(A),B),p),sc(conv(A,derivative(B)),q),-1n);
  if(C.length){
    check(W.length-1===d-D+m+n-1,'polynomial Wronskian degree identity');
    check(d>=D-m-n+1,'polynomial degree bound');
  } else check(!W.length,'equal powers give zero Wronskian');
}
const A=[0n,3n,0n,0n,0n,0n,125n],B=[1n,0n,0n,0n,0n,125n,0n,0n,0n,0n,3125n];
check(plus(power(B,3),power(A,5),-1n).length===16,'sparse binomial boundary degree');
check(plus(sc(conv(derivative(A),B),5),sc(conv(A,derivative(B)),3),-1n).length===1,'boundary constant Wronskian');

// Exact quadratic-ring calculation of the low-harmonic equation.
for(const D of [2n,3n,5n,6n]){
  const sum=([a,b],[c,d])=>[a+c,b+d];
  const product=([a,b],[c,d])=>[a*c+D*b*d,a*d+b*c];
  const scale=([a,b],s)=>[s*a,s*b];
  for(let d=-7n;d<=7n;++d) if(d) for(let x=-20n;x<=20n;++x) for(let y=-12n;y<=12n;++y){
    const a=[x,y],b=[x,-y],ab=product(a,b),a3=product(product(a,a),a);
    let v=sum([27n*d**3n,0n],scale(ab,18n*d));
    v=sum(sum(sum(v,scale(a3,-1n)),scale(a,-27n*d*d)),scale(product(b,b),-9n*d));
    check(v[1]===-y*(3n*(x-3n*d)**2n+D*y*y),'imaginary part of low-harmonic cancellation');
    if(!y) check(v[0]===-((x-3n*d)**3n),'rational part of low-harmonic cancellation');
    if(v[0]===0n && v[1]===0n) check(y===0n && x===3n*d,'only equal-power branch survives');
  }
}
console.log('Exact assertions passed: ' + checks);
