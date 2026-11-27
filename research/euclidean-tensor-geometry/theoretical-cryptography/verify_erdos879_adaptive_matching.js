"use strict";
let checked=0, geometryBins=0, exactProposals=0;
function ok(p,m){++checked;if(!p)throw Error(m);}
function gcd(a,b){for(;b;)[a,b]=[b,a%b];return a;}
function f(a,b=1n){a=BigInt(a);b=BigInt(b);const g=gcd(a,b);return[a/g,b/g];}
function mul(a,b){return f(a[0]*b[0],a[1]*b[1]);}
function inv(a){return f(a[1],a[0]);}
function sub(a,b){return f(a[0]*b[1]-b[0]*a[1],a[1]*b[1]);}
function cmp(a,b){return a[0]*b[1]-a[1]*b[0];}
function qInt(x,p){return BigInt(p)*x[1]-x[0];}
function inBin(p,bin){return qInt(bin[0],p)>0n&&qInt(bin[1],p)<=0n;}
const prime=[];
const sieve=new Uint8Array(450**2+1);
for(let p=2;p<sieve.length;++p)if(!sieve[p]){
  prime.push(p);
  for(let q=p*p;q<sieve.length;q+=p)sieve[q]=1;
}
function primesIn(bin){
  // Approximate endpoints are only used to get a search superset; exact membership is checked.
  const lo=Math.max(2,Math.floor(Number(bin[0][0]*100n/bin[0][1])/100)-1);
  const hi=Math.min(sieve.length-1,Math.ceil(Number(bin[1][0]*100n/bin[1][1])/100)+1);
  const selected=[];
  for(let p=lo;p<=hi;++p)if(!sieve[p]&&inBin(p,bin))selected.push(p);
  return selected;
}
for(let x of [128,216,343,450])for(let s of [20,38,50,71,83])for(let rate of [1,2,3,4]){
  const X=f(x),n=x*x;
  let t=mul(X,f(s,100));
  const pBins=[],qBins=[],weights=[];
  for(let j=0;j<80;++j){
    const h=f(rate*9+j,32000);
    const a=f(32000+rate*9+j,32000);
    const u=mul(t,a);
    const r=sub(f(1),mul(t,inv(X)));
    if(cmp(mul(f(16),h),r)>0n||cmp(u,X)>=0n)break;
    const low=mul(f(n),inv(mul(u,a)));
    const high=mul(f(n),inv(u));
    ok(cmp(low,X)>0n,"partner lower endpoint exceeds sqrt(N)");
    ok(cmp(t,u)<0n&&cmp(low,high)<0n,"nonempty bins");++geometryBins;
    if(j>0){
      ok(cmp(t,pBins.at(-1)[1])===0n,"adjacent demand bins");
      ok(cmp(high,qBins.at(-1)[0])<=0n,"disjoint descending supply bins");
    }
    pBins.push([t,u]);qBins.push([low,high]);weights.push(mul(f(n),inv(mul(a,a))));
    t=u;
  }
  const removed=new Set(),matches=[];
  let matchedDef=0;
  for(let j=0;j<pBins.length;++j){
    const demand=primesIn(pBins[j]), supply=primesIn(qBins[j]);
    for(let b=0;b<Math.min(demand.length,supply.length);++b){
      const p=demand[b],q=supply[b];++exactProposals;
      ok(p<=x&&q>x&&!removed.has(p)&&!removed.has(q),"distinct support");
      ok(p*q<=n&&cmp(f(p*q),weights[j])>0n,"exact pq interval");
      removed.add(p);removed.add(q);matches.push(p*q);
      matchedDef+=n-p*q+p+q;
    }
  }
  const squares=[];let squareDef=0;
  for(const p of primesIn([t,X])){
    ok(!removed.has(p)&&p*p<=n,"fresh square support");removed.add(p);
    ok(n-p*p<=2*x*(x-p),"near-square fallback cost");
    squares.push(p*p);squareDef+=n-p*p+p;
  }
  const baseline=prime.filter(p=>p<=n);
  const remaining=baseline.filter(p=>!removed.has(p));
  const full=[1,...remaining,...squares,...matches];
  const H=baseline.reduce((s,p)=>s+p,0)+n*baseline.filter(p=>p<=x).length;
  const missing=remaining.filter(p=>p<=x).length;
  ok(H-full.reduce((s,a)=>s+a,0)===matchedDef+squareDef+n*missing-1,"exact construction deficit");
  ok(H-full.reduce((s,a)=>s+a,0)>=baseline.filter(p=>p<=x).reduce((s,p)=>s+p,0)-1,"budget lower bound");
}
console.log(JSON.stringify({assertions:checked,geometryBins,exactProposals}));
