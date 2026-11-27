"use strict";

// Exact-arithmetic sanity checks for small, positive integer weights.
// Run: node verify_factor_erdos1100_superincreasing_merge.js
let checked=0, merges=0, full=0;
const assert=(ok,what)=>{ ++checked; if(!ok) throw Error(what); };
const fib=[0,1];
for(let j=2;j<=30;++j) fib[j]=fib[j-1]+fib[j-2];
let rng=0xa18c91a1;
function rand(n) {
  rng=(Math.imul(rng,1664525)+1013904223)>>>0;
  return (rng>>>11)%n;
}
function sums(w) {
  const a=[0];
  for(const x of w) {const n=a.length; for(let i=0;i<n;++i) a.push(a[i]+x);}
  return a; // index is mask
}
function merge(a,t) {
  let i=0,j=0,last=-1,color=-1,count=0;
  while(i<a.length||j<a.length) {
    const x=i<a.length ? a[i]:Infinity;
    const y=j<a.length ? a[j]+t:Infinity;
    if(x===y) throw Error("unexpected tie");
    const c=x<y?0:1;
    const u=c===0?i++:j++;
    if(color!==-1&&c!==color&&(u&last)===0) ++count;
    last=u; color=c;
  }
  ++merges;
  return count;
}
function test(ws) {
  let prev=[0], oldSum=0, oldP=1,oldQ=2;
  for(let m=1;m<=ws.length;++m){
    const w=ws[m-1],sum=oldSum+w,a=sums(ws.slice(0,m));
    assert(a[a.length-1]===sum&&a.every((x,i)=>i===0||x>a[i-1]),"binary order");
    let dis=0;
    for(let i=1;i<a.length;++i) if((i&(i-1))===0)++dis;
    assert(dis===m,"internal count");
    let p=0,q=0;
    const counts=[];
    // All differences are even. One odd representative per open cell.
    // At an even value that is not a tie, at least one neighboring cell gives
    // the same order. All shifts above sum have the same count.
    for(let t=1;t<=sum+1;t+=2) {
      const actual=merge(a,t);
      let bound=merge(prev,Math.abs(t-w));
      if(t<=oldSum) bound+=merge(prev,t);
      else if(t<w) ++bound;
      assert(actual<=bound,"two types");
      assert(actual<=2*fib[m+1],"first Fibonacci bound");
      counts.push(actual);
      p=Math.max(p,actual);
    }
    const top=counts.slice();
    for(let i=top.length-2;i>=0;--i) top[i]=Math.max(top[i],top[i+1]);
    for(let i=0;i<counts.length;++i) {
      // A pair of open cells of widths 2 with odd centers x,y admits
      // a+b>sum exactly when x+y>=sum. The last cell is unbounded and
      // its chosen center sum+1 already works with every other cell.
      const x=2*i+1;
      const j=Math.max(0,Math.ceil((sum-x-1)/2));
      if(j<top.length) q=Math.max(q,counts[i]+top[j]);
    }
    assert(p<=Math.max(oldQ,1+oldP),"P recurrence");
    assert(q<=Math.max(2+2*oldP,oldQ+oldP),"Q recurrence");
    assert(q<=2*fib[m+2],"paired Fibonacci bound");
    oldP=p; oldQ=q; oldSum=sum; prev=a;
  }
}
function testExtras(ws,r) {
  const m=ws.length, scale=2**r;
  const w=ws.map(x=>scale*x);
  for(let j=0;j<r;++j) w.push(scale*(1+rand(ws.reduce((a,b)=>a+b,0)+10))+(1<<j));
  const ordered=sums(w).map((v,mask)=>[v,mask]).sort((x,y)=>x[0]-y[0]);
  let count=0;
  for(let i=1;i<ordered.length;++i) {
    assert(ordered[i-1][0]<ordered[i][0],"distinct sums modulo scale");
    if((ordered[i-1][1]&ordered[i][1])===0)++count;
  }
  assert(count<=m+(3**r-1)*fib[m+1],"full exceptional bound");
  if(r===0) assert(count===m,"no-exception equality");
  ++full;
}
const fixtures=[];
for(let m=1;m<=8;++m) {
  fixtures.push(Array.from({length:m},(_,j)=>2**(j+1)));
  for(let i=0;i<9;++i) {
    const w=[];let total=0;
    for(let j=0;j<m;++j) {const x=total+2+2*rand(8); total+=x; w.push(x);}
    fixtures.push(w);
  }
}
for(const w of fixtures) {
  test(w);
  for(let r=0;r<=3;++r) for(let i=0;i<(r?4:1);++i) testExtras(w,r);
}
console.log("PASS: "+checked+" exact assertions, "+merges+" merge sweeps, "
            +full+" full configurations across "+fixtures.length+" deterministic bases");
