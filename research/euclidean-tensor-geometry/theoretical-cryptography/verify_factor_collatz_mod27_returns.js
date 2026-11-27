"use strict";
// Exact checks for the mod-27 certificate and the rational witness construction.
// Run: node verify_factor_collatz_mod27_returns.js
const assert=require("node:assert/strict");
let checks=0;
function check(p,label){++checks;assert.ok(p,label);}
function mod(x,m){return ((x%m)+m)%m;}
function gcd(a,b){while(b!==0n)[a,b]=[b,a%b];return a;}
const H = [null,3,2,null,1,2,null,3,1,null,3,2,null,1,2,null,3,1,null,3,0,null,1,2,null,3,0];
function next(r,p){return (14*(p?3*r+1:r))%27;}
function T(x){return ((x&1n)?3n*x+1n:x)/2n;}
const vv=Array.from({length:27},(_,i)=>i).filter(i=>i%3!==0);
function edge(r,p){
  const s=next(r,p), j=+(r===20), e=+(r===26&&s===26);
  check(H[r]-H[s]+2*j+e>=2*p-1, "potential");
  return s;
}
for(const r of vv){
  check(H[r]>=0&&H[r]<=3,"range");
  for(const p of [0,1]){
    const s=edge(r,p);
    const sample=BigInt(54+r+27*((r&1)^p));
    check(Number(T(sample)%27n)===s,"actual branch");
  }
}
check(H[26]===0&&H[20]===0,"loop and cut levels");
check(next(26,0)===13&&next(13,0)===20&&next(13,1)===20,"forced exit");
let r=2,j=0,t=0;
for(const p of [1,1,0,1,0,1]){
  j+=+(r===20);
  r=edge(r,p);
  t+=p;
}
check(r===2&&j===1&&t===4&&next(26,1)===26,"tight witnesses");
check(10n**4n<2n**7n*3n**4n,"odd-count logarithm comparison");
check(12n**3n<2n**4n*5n**3n,"cost logarithm comparison");
check(3n**2n>2n**3n&&3n**5n<2n**8n,"alpha brackets");
check(3n**7n>2n**11n&&3n**29n<2n**46n,"refined alpha brackets");
check(97n**5n<2n**8n*32n**5n,"floor 32 gives odd surplus above 1/4");
check(56n*1000000n>9n*133n*46057n,"Rhin exponent constant < 56/9");
const N0=(355504839929n+1n)/2n;
check(N0<2n**38n&&N0*29n**37n>6450n*46n**37n,"38 distinct visits cutoff");

function pathCheck(xs,maxSteps){
  let x=xs,q=0,J=0,L=0,N=0, blockRuns=0,onLoop=false, events=0;
  const b=(xs+1n).toString(2).length;
  let pow5=1n,pow8=1n;
  if(xs%3n===0n)return 0;
  while(x>=3n&&N<maxSteps){
    const p=Number(x&1n),r=Number(x%27n),y=T(x),s=Number(y%27n);
    const loop=r===26&&s===26;
    if(r===20){++J;pow5*=5n;pow8*=8n;blockRuns=0;}
    if(loop&&!onLoop){++blockRuns;check(blockRuns===1,"one run per cut block");}
    onLoop=loop;
    q+=p; L+=+loop; ++N;
    check(2*q-N<=2*J+L+H[Number(xs%27n)]-H[s],"summed path potential");
    if(y>=xs){
      check(BigInt(N)*pow5<7n*BigInt(25+3*b)*pow8,"finite path bound at 8/5");
      ++events;
    }
    x=y;
  }
  return events;
}
let events=0;
for(let x=3n;x<=18000n;x++) events+=pathCheck(x,180);
for(let e=1n;e<=160n;e++){
  const x=27n*(1n<<e)-1n, u=x+1n;
  let y=x;
  for(let i=0n;i<e;i++){
    check(y%27n===26n&&(y&1n)===1n,"marker-free odd burst");
    y=T(y);
  }
  check(y+1n===27n*3n**e&&(y&1n)===0n,"exact burst endpoint");
  check(u===27n*2n**e&&T(T(y))%27n===20n,"post-burst marker");
  events+=pathCheck(x,320);
}
check(events>75000,"nondecreasing endpoint coverage");

function repeated(w,reps){let out=[];for(let i=0;i<reps;++i)out.push(...w);return out;}
function word(N,q){
  const k=2*q-N-2,l=N-q-2;
  check(k>=0&&l>=0,"integer block counts");
  const w=[1,1,...Array(k).fill(1),0,1,0,1,...repeated([0,1],l)];
  check(w.length===N&&w.reduce((a,b)=>a+b,0)===q,"counts");
  return w;
}
function expansion(w){
  let a=1n,c=0n,b=1n;
  for(const p of w){
    if(p){a*=3n;c=3n*c+b;}
    b*=2n;
  }
  return {a,c,b,d:b-a};
}
function checkWitness(N,q,M,L){
  const w=word(N,q),{a,c,b,d}=expansion(w),Q=BigInt(M);
  check(d>0n&&d<a&&gcd(d,54n*Q)===1n,"positive and permitted denominator");
  check((N-1)%L===0&&(q-1)%L===0,"progressions");
  let u=c,r=2,hits=0,position=0,min=c;
  for(const p of w){
    check(u>0n&&(u&1n)===BigInt(p)&&mod(u-BigInt(r)*d,27n)===0n,"rational state and class");
    check(u*3n>=a,"each state is at least a/(3D)");
    if(u<min)min=u;
    hits+=+(r===20);r=next(r,p);
    u=((p?3n*u+d:u)>>1n);
    ++position;
  }
  check(u===c&&r===2&&hits===1&&position===N,"closed with exactly one marked departure");
  check(3n*min<=BigInt(q)*b,"upper bound for the minimum");
  check(gcd(c,d)<d,"noninteger");

  // Lift one full prescribed rational lap modulo Q and 27 to an actual integer trajectory.
  const m=54n*Q*2n**BigInt(N), testQ=27n*Q, dSmall=d%testQ;
  // The product 54*M is coprime to d, so use the exact extended Euclidean algorithm.
  let x0=1n,x1=0n,a0=d,a1=m;
  while(a1!==0n){const k=a0/a1;[a0,a1]=[a1,a0-k*a1];[x0,x1]=[x1,x0-k*x1];}
  check(a0===1n,"inverse exists");
  let y=mod(c*x0,m)+m;
  u=c;
  for(const p of w){
    check((y&1n)===BigInt(p)&&mod((y%testQ)*dSmall-u%testQ,testQ)===0n,"integer shadow");
    y=T(y);u=(p?3n*u+d:u)/2n;
  }
  check(mod((y%testQ)*dSmall-u%testQ,testQ)===0n,"shadow endpoint");
  return {N,q,M};
}
const witnesses=[];
// Floating point locates candidates only. Every claimed witness is checked by BigInt.
for(const [M,L,maxQ] of [[1,1,350],[25,20,35000],[77,30,60000],[385,60,60000]]){
  let best=null,bestGap=0.48;
  for(let q=1+L;q<=maxQ;q+=L){
    const N=1+L*Math.ceil((Math.log2(3)*q-1)/L),gap=N-Math.log2(3)*q;
    if(gap>0&&gap<bestGap){bestGap=gap;best={N,q};}
  }
  check(best!==null,"witness located");
  witnesses.push(checkWitness(best.N,best.q,M,L));
}
console.log(JSON.stringify({checks,nondecreasingEndpoints:events,witnesses}));
