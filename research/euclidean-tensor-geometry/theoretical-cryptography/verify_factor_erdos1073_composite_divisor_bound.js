"use strict";
// Finite, exact arithmetic checks. No numerical assumptions in the proof.
let checks=0;
function test(x,why){++checks;if(!x)throw Error(why);}
const X=200000,S=Math.floor(Math.sqrt(X-1));
const spf=new Int32Array(X);
for(let p=2;p<X;p++)if(!spf[p])for(let j=p;j<X;j+=p)if(!spf[j])spf[j]=p;
const primes=[];for(let p=2;p<=S;p++)if(spf[p]===p)primes.push(p);
const W=new Map();
let witnessPairs=0;
for(const p of primes){
  let f=1;const seq=[];
  for(let n=1;n<p;n++){f=f*n%p;if(f===p-1)seq.push(n);}
  const hist=new Map();
  for(let i=0;i<seq.length;i++)for(let j=i+1;j<seq.length;j++){
    const d=seq[j]-seq[i];
    let g=1;for(let h=1;h<=d;h++)g=g*(seq[i]+h)%p;
    test(g===1,"factorial ratio identity");
    hist.set(d,(hist.get(d)??0)+1);++witnessPairs;
  }
  for(const [d,m] of hist)test(m<=d,"polynomial pair bound");
  W.set(p,new Set(seq));
}
function binom(n,k){if(n<k)return 0n;let v=1n;for(let j=1;j<=k;j++)v=v*BigInt(n-j+1)/BigInt(j);return v;}
const cutoff=(p,k)=>BigInt(p)**BigInt(4*k+3)<=BigInt(X)**4n;
const layers={},below={};
for(let u=4;u<X;u++){
  const p=spf[u];
  if(p===u)continue;
  let z=u,k=0;while(z>1){z/=spf[z];++k;}
  let f=1;
  for(let n=1;n<p;n++){
    f=f*n%u;
    if(f===u-1){
      test(k<=n&&p>=k+1,"witness and prime-factor capacity");
      test(W.get(p).has(n),"witness survives both moduli");
      layers[k]=(layers[k]??0)+1;
      if(cutoff(p,k))below[k]=(below[k]??0)+1;
      break;
    }
  }
}
for(const [key,count] of Object.entries(below)){
  const k=+key;
  let cap=0n;
  for(const p of primes)if(cutoff(p,k))
    for(const n of W.get(p))cap+=binom(n,k-1);
  test(BigInt(count)<=cap,"small-prime labeled-factor capacity");
}
let factorial=1;
for(let n=1;n<=12;n++){
  factorial*=n;
  let z=factorial+1;let cap=0;
  for(let p=2;p*p<=z;p++)while(z%p===0){z/=p;++cap;test(p>n,"prime exceeds witness");}
  if(z>1){++cap;test(z>n,"last prime exceeds witness");}
  test(cap<=n,"exact multiplicity bound on the full shifted factorial");
}
function gcd(a,b){for(;b;)[a,b]=[b,a%b];return a;}
function frac(a,b){const g=gcd(a,b);return [a/g,b/g];}
const add=(x,y)=>frac(x[0]*y[1]+y[0]*x[1],x[1]*y[1]);
const mul=(x,y)=>frac(x[0]*y[0],x[1]*y[1]);
const lt=(x,y)=>x[0]*y[1]<y[0]*x[1];
function fact(k){let v=1n;for(let j=2n;j<=k;j++)v*=j;return v;}
const logTerm=j=>frac(2n,(2n*j+1n)*4n**(2n*j+1n));
const layerTerm=k=>frac((3n*k+2n)*2n**(k-1n),3n**k*fact(k-1n)*fact(k));
let lower=[0n,1n];
for(let j=0n;j<8n;j++)lower=add(lower,logTerm(j));
for(let k=3n;k<9n;k++)lower=add(lower,layerTerm(k));
const upper=add(add(lower,mul(logTerm(8n),[16n,15n])),mul(layerTerm(9n),[10n,9n]));
test(lt([656628n,1000000n],lower)&&lt(upper,[656630n,1000000n]),"rigorous enclosure");
test(lt(upper,[657n,1000n]),"constant below 0.657");
console.log({checks,X,layers,below,witnessPairs});
