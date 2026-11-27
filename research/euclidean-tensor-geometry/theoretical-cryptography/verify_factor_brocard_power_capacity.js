"use strict";
// Exact finite checks for the prime-power capacity note. No square search beyond n=110.
const assert=require("node:assert/strict");
let checks=0, splits=0;
function check(x,s){++checks;assert.ok(x,s);}
function gcd(a,b){while(b)[a,b]=[b,a%b];return a;}
function exactPrimes(n){
  const P=[];
  for(let a=2;a<=n;a++){
    if(P.every(p=>p*p>a||a%p!==0))P.push(a);
  }
  return P;
}
function exponent(n,p){let e=0;for(;n>=p;){n=Math.floor(n/p);e+=n;}return e;}
function valuation(n,p){let k=0;while(n%p===0n){n/=p;++k;}return k;}
function integerSqrt(n){
  if(n<2n)return n;
  let y=1n<<BigInt(Math.ceil(n.toString(2).length/2));
  while(true){const z=(y+n/y)>>1n;if(z>=y)return y;y=z;}
}
const fact=[1n];
for(let n=1;n<=230;n++)fact.push(BigInt(n)*fact[n-1]);

// e^14 > 10^6 from the positive Taylor partial sum with a common denominator.
let z=0n;
for(let j=0;j<=26;j++)z+=14n**BigInt(j)*(fact[26]/fact[j]);
check(z>1000000n*fact[26],"ln(10^6)<14");
check(20n*(18n*125n-7n*29n)>11n*29n*125n,"logarithmic margin >11/20");
check(19n*10n<1000000n,"tiny factorial and division-by-four error");
for(const [k,B] of [[15811n,10n**9n],[15811388n,10n**15n]]){
  check(4n*k*k<B&&4n*(k+1n)**2n>B,"k-free cutoff");
  check(integerSqrt(B)/2n===k,"√B/2 floor");
}

for(let n=1;n<=230;n++){
  for(let u=1;u<=n;u++){
    const q=Math.floor(n/u);
    const block=fact[u]**BigInt(q);
    check(fact[n]%block===0n,"factorial power block divides");
    if(u>=4){
      check(block%4n===0n&&(fact[n]/4n)%(block/4n)===0n,"normalized block divides");
      let odd=block;
      while((odd&1n)===0n)odd>>=1n;
      check((fact[n]/4n)%odd===0n,"odd block divides");
    }
  }
  for(const p of exactPrimes(n)){
    const P=BigInt(p),e=exponent(n,p);
    check(valuation(fact[n],P)===e,"Legendre matches factorial valuation");
    for(let K=1;K<=n;K++){
      if(p*K<=n)check(e>=K,"lower exponent threshold");
      if(e>=K)check((p-1)*K<=n,"upper exponent threshold");
      if(p*p>n)check((e<K)===(p*K>n),"no low/high ambiguity in large-prime range");
    }
  }
}

for(let n=4;n<=47;n++){
  const N=fact[n]/4n, p=exactPrimes(n).slice(1), d=2n**BigInt(exponent(n,2)-2);
  const data=p.map(x=>[exponent(n,x),BigInt(x)**BigInt(exponent(n,x))]);
  check(d*data.reduce((a,b)=>a*b[1],1n)===N,"normalized full blocks");
  for(let K=1;K<=7;K++){
    const highs=data.filter(x=>x[0]>=K).map(x=>x[1]).sort((a,b)=>a>b?-1:a<b?1:0);
    const low=data.filter(x=>x[0]<K).reduce((a,b)=>a*b[1],1n);
    const maximum=[];
    for(let h=0,m=low;h<=highs.length;h++){maximum.push(m);m*=highs[h]??1n;}
    const actual=Array(highs.length+1).fill(0n);
    function f(i,m,h){
      if(i===data.length){
        ++splits;
        check(m<=maximum[h]&&gcd(m,N/m)===1n,"capacity and odd unitary divisor");
        check(m*d<=maximum[h]*d&&gcd(m*d,N/(m*d))===1n,"capacity and even unitary divisor");
        if(actual[h]<m)actual[h]=m;
        return;
      }
      f(i+1,m,h);f(i+1,m*data[i][1],h+ +(data[i][0]>=K));
    }
    f(0,1n,0);
    for(let i=0;i<actual.length;i++){
      check(actual[i]===maximum[i],"odd saturation");
    }
  }
}

const roots=[];
for(let n=1;n<=110;n++){
  const N=fact[n]+1n,m=integerSqrt(N);
  check(m*m<=N&&(m+1n)**2n>N,"integer square-root bracket");
  if(m*m!==N)continue;
  roots.push(n);
  const a=(m-1n)/2n,b=a+1n;
  check(a*b===fact[n]/4n&&gcd(a,b)===1n,"known pair normalized");
}
check(JSON.stringify(roots)==="[4,5,7]","small controls only");
console.log(JSON.stringify({checks,splits,roots}));
