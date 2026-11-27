"use strict";
// Exact finite CRT and coprime-certificate tests; no numerical evidence for asymptotic sieve bounds.
let checks=0, residueDraws=0, visitedSets=0;
function ok(condition,msg) { ++checks; if(!condition) throw Error(msg); }
const ps=[2,3,5,7,11,13,17,19,23,29,31,37];
const product=a=>a.reduce((b,c)=>b*c,1n);
function factors(n) { return ps.filter(p=>n%p===0); }
function gcd(a,b) { for(;b;) [a,b]=[b,a%b]; return a; }
function lcm(a,b) { return a/gcd(a,b)*b; }
function vpNum(pList,y) { return product(pList.filter(p=>p<=y).map(p=>BigInt(p-1))); }
function vpDen(pList,y) { return product(pList.filter(p=>p<=y).map(BigInt)); }
function modelTests(pList,ds,g) {
  const Q=Number(product(pList.map(BigInt)));
  const m=ds.length;
  const counts=new Int32Array(m);
  const evenCounts=new Int32Array(m);
  const pair=Array.from({length:m},()=>new Int32Array(m));
  for(let n=0;n<Q;++n) {
    ++residueDraws;
    const good=[];
    for(let i=0;i<m;++i) if(pList.every(p=>p>g(ds[i])||(n-ds[i])%p!==0)) {
      good.push(i); ++counts[i];
      if(n%2===0) ++evenCounts[i];
    }
    for(let i=0;i<good.length;++i)
      for(let j=i+1;j<good.length;++j) ++pair[good[i]][good[j]];
  }
  for(let i=0;i<m;++i) {
    const d=ds[i], y=g(d), M=vpNum(pList,y), D=vpDen(pList,y);
    ok(BigInt(counts[i])*D===BigInt(Q)*M,"CRT single indicator");
    if(y>=2) ok(BigInt(evenCounts[i])*D===BigInt(Q)*(d%2?M:0n),"parity projection");
    for(let j=i+1;j<m;++j) {
      const e=ds[j], z=g(e), h=e-d;
      const Cnum=product(pList.filter(p=>p<=y).map(p=>BigInt(p*(p-2+Number(h%p===0)))));
      const Cden=product(pList.filter(p=>p<=y).map(p=>BigInt((p-1)**2)));
      const left=BigInt(pair[i][j])*D*vpDen(pList,z)*Cden;
      const right=BigInt(Q)*M*vpNum(pList,z)*Cnum;
      ok(left===right,"CRT covariance kernel");
      if(y>=2&&h%2) ok(pair[i][j]===0,"odd-gap exclusion at 2");
    }
  }
}
for(let y of [3,7,11,13,17]) {
  const pList=ps.filter(p=>p<=y);
  modelTests(pList,Array.from({length:y-1},(_,j)=>j+2),d=>d);
  modelTests(pList,Array.from({length:y+2},(_,j)=>j+4),d=>Math.floor(Math.sqrt(d)));
  if(y<=7) modelTests(pList,Array.from({length:30},(_,j)=>j+16),d=>Math.min(y,Math.floor(d/(2*Math.log(d)))));
}
for(let y=2;y<=17;++y) {
  const pList=ps.filter(p=>p<=y);
  const Q=product(pList.map(BigInt));
  let coef=[[1n,1n]],D=1n;
  for(const p of pList) {
    const P=BigInt(p),a=P*(P-2n),b=P;
    coef=coef.flatMap(([q,c])=>[[q,a*c],[q*P,b*c]]);
    D*=((P-1n)**2n);
  }
  const tot=coef.reduce((s,[q,c])=>s+c,0n);
  ok(coef.reduce((s,[q,c])=>s+c*(Q/q),0n)===Q*D,"finite product mean is exactly 1");
  ok(tot*vpNum(pList,y)===D*vpDen(pList,y),"total coefficient cost");
  for(let H=0;H<=1900;++H) {
    const B=BigInt(H);
    const S=coef.reduce((s,[q,c])=>s+c*(B/q),0n) - B*D;
    ok(S<=0n&&S>=-tot,"signed floor error, without independent-offset assumption");
  }
}
for(let max=4;max<=4000;max+=17) for(let min of [4,7,14]) if(min<max) {
  const used=new Int8Array(max+1);
  let B=max;
  for(;B>min;) {
    const A=Math.max(min,Math.sqrt(B));
    ok(B<=A*A+1e-10,"real band width condition B<=A^2");
    for(let k=Math.floor(A)+1;k<=B;++k)++used[k];
    B=A;
  }
  for(let k=min+1;k<=max;++k) ok(used[k]===1,"exact band boundary partition");
}
for(let n=2;n<=30;++n) {
  let common=1n; for(let d=1;d<n;++d) common=lcm(common,BigInt(d));
  const weights=Array.from({length:n},(_,a)=>a?common/BigInt(n-a):0n);
  function first(a) {return a===1?Infinity:factors(a)[0];}
  const lo=[],hi=[];
  for(let a=1;a<n;++a) {
    const d=n-a;
    if(first(a)>d)lo.push(a);
    if(d>=16&&first(a)>d/(2*Math.log(d)))hi.push(a);
  }
  for(let i=0;i<lo.length;++i)for(let j=0;j<i;++j)
    ok(gcd(BigInt(lo[i]),BigInt(lo[j]))===1n,"self-rough choices are pairwise coprime");
  const loW=lo.reduce((s,a)=>s+weights[a],0n);
  const hiW=hi.reduce((s,a)=>s+weights[a],0n);
  let best=0n;
  function choices(a,mask,w) {
    if(a===n){++visitedSets;if(w>best)best=w;return;}
    choices(a+1,mask,w);
    const pm=a===1?0:factors(a).reduce((m,p)=>m|(1<<ps.indexOf(p)),0);
    if(!(mask&pm))choices(a+1,mask|pm,w+weights[a]);
  }
  choices(1,0,0n);
  ok(loW<=best,"all self-rough weights below the exact coprime maximum");
  let staticCost=common+Array.from({length:Math.min(15,n-1)},(_,i)=>common/BigInt(i+1)).reduce((s,x)=>s+x,0n);
  for(let p of ps.filter(p=>p<n)) {
    // For these small p, 2/p majorizes 1/(p log p).
    staticCost+=2n*common/BigInt(p);
  }
  ok(best<=hiW+staticCost,"rough upper bound plus a finite prime cost");
}
console.log(JSON.stringify({assertions:checks,crtResidueDraws:residueDraws,exactCoprimeSets:visitedSets}));
