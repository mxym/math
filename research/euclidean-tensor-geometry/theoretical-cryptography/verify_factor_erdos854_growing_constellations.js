"use strict";
// Exact small instances of the uniform-transfer bookkeeping.
let checks=0;
function test(x,why){++checks;if(!x)throw Error(why);}
const mod=(a,p)=>(a%p+p)%p;
const bigmod=(a,p)=>(a%p+p)%p;
const bases=[2,3,5,7,11,13], reserves=[17,19,23,29,31], primes=[...bases,...reserves];
const product=primes.reduce((N,p)=>N*BigInt(p),1n);
function inv(a,p){
  for(let e=1n;e<p;++e)if(a*e%p===1n)return e;
  throw Error("not invertible");
}
const weights=new Map(primes.map(p=>{
  const q=BigInt(p),a=product/q;return [p,a*inv(a%q,q)];
}));
function solve(cs){
  return bigmod([...cs].reduce((v,[p,b])=>v+weights.get(p)*BigInt(-b),0n),product);
}
function gcd(a,b){for(;b;)[a,b]=[b,a%b];return a;}
const fixtures=[
  [2183,17,2,[0,4,6,12],12],
  [5749,17,4,[0,6,8,12],6],
  [9439,21,4,[0,2,6,14],16],
  [9439,21,4,[0,2,8,14],16],
];
let bans=0, assignments=0, wraps=0, checkedStarts=0;
for(const [t0,Y,m,hs,hole] of fixtures){
  const old=new Map(bases.map(p=>[p,mod(-t0,p)]));
  const H=hs[hs.length-1], protectedPositions=hs.map(h=>m+h);
  const hits=(cs,n)=>[...cs].some(([p,b])=>n%p===b);
  const avoids=(p,b)=>protectedPositions.every(n=>n%p!==b);
  test(primes.every(p=>new Set(hs.map(h=>h%p)).size<p),"admissible");
  test(m+H<=Y,"window in original cover");
  for(let n=1;n<=Y;n++)test(hits(old,n),"original cover");
  test([2,3].every(p=>avoids(p,old.get(p))),"safe at the first two primes");
  const kept=new Map([...old].filter(([p,b])=>avoids(p,b)));
  const holes=[];
  for(let n=m;n<=m+H;n++)if(!hits(kept,n)&&!protectedPositions.includes(n))holes.push(n);
  test(holes.length===1&&holes[0]===hole,"actual uncovered nonprescribed point");
  const bad=reserves.filter(p=>!avoids(p,hole%p));
  test(bad.length<=hs.length,"conflict bound");
  const repair=reserves.find(p=>!bad.includes(p));kept.set(repair,hole%repair);
  ++assignments;
  const choices=p=>Array.from({length:p},(_,b)=>b).filter(b=>avoids(p,b));
  for(const p of bases)if(!kept.has(p))kept.set(p,choices(p)[0]);
  for(let n=m;n<=m+H;n++)test(hits(kept,n)!==protectedPositions.includes(n),"after repair");
  const free=reserves.filter(p=>p!==repair);
  const varying=free.slice(-3);
  for(const p of free)if(!varying.includes(p))kept.set(p,choices(p)[0]);
  const seen=new Set();let removed=0;
  for(const a of choices(varying[0]))for(const b of choices(varying[1]))for(const c of choices(varying[2])){
    [a,b,c].forEach((v,i)=>kept.set(varying[i],v));
    const u=bigmod(solve(kept)+BigInt(m),product);
    const keep=u>=1n&&u+BigInt(H)<product;
    if(!keep)++removed;
    test(!seen.has(u),"injective CRT completions");seen.add(u);
    for(let i=0;i<=H;i++)test((gcd(u+BigInt(i),product)===1n)===hs.includes(i),"exact pattern");
    ++checkedStarts;
  }
  test(seen.size===varying.reduce((a,p)=>a*(p-new Set(hs.map(h=>h%p)).size),1),"full independent product");
  test(removed<=H+1,"deletion for the literal-list boundary");
  for(const M of [11,23,99,333]){
    const small=[2,3,5,7];
    const events=small.map(p=>new Set(hs.map(h=>mod(old.get(p)-h,p))));
    const counts=[];
    for(let mask=0;mask<(1<<small.length);mask++){
      const factors=small.map((_,i)=>i).filter(i=>(mask>>i)&1);
      const cycle=factors.reduce((n,i)=>n*small[i],1);
      const residueProduct=factors.reduce((n,i)=>n*events[i].size,1);
      const meets=u=>factors.every(i=>events[i].has(u%small[i]));
      let crt=0,finite=0;
      for(let u=1;u<=cycle;u++)if(meets(u))++crt;
      for(let u=1;u<=M;u++)if(meets(u))++finite;
      test(crt===residueProduct,"full CRT intersection count");
      test(Math.abs(cycle*finite-M*residueProduct)<=cycle*residueProduct,"interval rounding count");
      counts.push([factors.length,finite]);
    }
    const actual=Array.from({length:M},(_,i)=>i+1).filter(u=>small.every((p,i)=>!events[i].has(u%p))).length;
    for(let j=1;j<=3;j+=2){
      test(counts.filter(x=>x[0]<=j).reduce((a,[k,n])=>a+(-1)**k*n,0)<=actual,"odd Bonferroni bound");
      ++bans;
    }
  }
}
// A separate wrapping constellation, 1 following P-1 with zero between.
const u=product-1n;
test(gcd(u,product)===1n&&gcd(u+1n,product)>1n&&gcd(u+2n,product)===1n,"true cyclic but not internal");
for(let h=1;h<=80;h++){
  let removed=0;
  for(let a=0n;a<=BigInt(h);a++)if(!(a>=1n&&a+BigInt(h)<product))++removed;
  for(let a=product-BigInt(h);a<product;a++)if(!(a>=1n&&a+BigInt(h)<product))++removed;
  test(removed===h+1,"exact boundary exclusion cardinality");++wraps;
}
console.log({checks,checkedStarts,assignments,bonferroni:bans,wraps});
