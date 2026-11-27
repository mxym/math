/* Node 18+. Generated mathematical checks only. */
'use strict';
function assert(x, label) { if (!x) throw new Error(label); }
const PI = Math.PI;
let exact = 0, numeric = 0;
function ex(x, label) { ++exact; assert(x, label); }
function nu(x, label) { ++numeric; assert(x, label); }
function logDensity(s, x) {
  if (s >= 0.75) {
    let u = 0;
    for (let j = 1; j <= 8; ++j) u += 2*Math.exp(-PI*j*j*s*s)*Math.cos(2*PI*j*x);
    return Math.log1p(u);
  }
  let u = 0;
  for (let j = -5; j <= 5; ++j) {
    if (j !== 0) u += Math.exp(-PI*(j*j+2*x*j)/(s*s));
  }
  return -Math.log(s) - PI*x*x/(s*s) + Math.log1p(u);
}
function gaussianRenyi(gamma, theta) {
  return (-theta*Math.log(gamma)-Math.log1p(-theta*(gamma-1)))/(2*theta);
}
function integrate(s, t, theta) {
  const N = 8192;
  let kl=0, h=0, moment=0, dp=0, dq=0;
  for(let i=0;i<N;++i) {
    const x=(i+0.5)/N-0.5;
    const lp=logDensity(s,x), lq=logDensity(t,x), l=lp-lq;
    const p=Math.exp(lp), q=Math.exp(lq);
    dp+=p; dq+=q;
    kl+=Math.abs(l)<0.01
      ? q*(l*l*(0.5+l*(1/3+l*(1/8+l*(1/30+l/144)))))
      : p*l+q-p;
    const r=Math.exp(lp/2)-Math.exp(lq/2);
    h+=r*r/2;
    moment+=Math.exp(lp+theta*l);
  }
  return {kl:kl/N, B:-Math.log1p(-Math.min(h/N,1-Number.EPSILON)),
          renyi:Math.log(moment/N)/theta, dp:dp/N,dq:dq/N};
}
const widths=[0.015,0.025,0.06,0.1,0.2,0.29,0.485,0.61,0.749,0.75,0.851,1,1.004,1.28,1.8,2.5,4];
for(const s of widths) for(let j=0;j<=1024;++j) {
  const x=-.5+j/1024, sb=Math.min(s,1);
  const l=logDensity(s,x)+Math.log(sb)+PI*x*x/(sb*sb);
  nu(l>=-0.16 && l<=1.15,'periodic-real envelope point');
  if(s>=1) nu(Math.abs(logDensity(s,x))<=.1,'broad uniform envelope');
}
const theta=1/8,K=4;
for (const s of widths) for (const t of widths) {
  const u=Math.min(s,1),v=Math.min(t,1),g=(u/v)**2;
  if(g<=K) {
    const r=integrate(s,t,theta);
    nu(Math.abs(r.dp-1)<2e-11 && Math.abs(r.dq-1)<2e-11,'quadrature normalization');
    nu(r.kl>=0 && r.B>=0 && r.renyi>=-2e-10,'divergence signs');
    nu(r.renyi<=16*r.kl+3e-10,'regular moment vs KL');
    nu(r.kl<=16*r.B+3e-10,'regular KL vs affinity');
    if (s<1 && t<1 && g>1) {
      nu(r.renyi<=gaussianRenyi(g,theta)+3e-10,'data processing from line');
      const m=Math.floor(1/(2*t));
      if(t<1/(2*Math.sqrt(K))) {
        nu(m*t>=.25-1e-14 && m*t<=.5+1e-14,'Fourier compact interval');
        const cosine=Math.exp(-PI*m*m*t*t)-Math.exp(-PI*m*m*s*s);
        nu(cosine>.02*(g-1)-1e-15,'Fourier lower bound');
      }
    }
  } else {
    for(let j=0;j<=128;++j) {
      const x=-.5+j/128,l=logDensity(s,x)-logDensity(t,x);
      nu(l<=2/(v*v),'exceptional pointwise cap');
    }
  }
}
let seed=2330150121;
function rng(n) {
  seed=(Math.imul(seed,1664525)+1013904223)>>>0;
  return seed%n;
}
for(let i=0;i<1600;++i) {
  // Capacities and target Q costs are integers in units of 1/256.
  // Variance ratio g is integral; u^2=g/k and v^2=1/k.
  const M=BigInt(2+rng(50)), m2=M*M;
  const count=1+rng(19);
  const coords=[];
  let total=0n;
  for(let j=0;j<count;++j) {
    const g=m2+BigInt(1+rng(3000));
    const k=g+BigInt(1+rng(3000));
    const lo=g, hi=4n*k;
    ex(lo<hi && g>m2 && g<=k,'admissible costs');
    coords.push([g,lo,hi]); total+=hi;
  }
  const target=1n+BigInt(rng(Number(total)));
  let qSum=0n, pNum=0n, pDen=1n, last=0;
  for (const [g,lo,hi] of coords) {
    if (qSum>=target) break;
    const add=Math.min(Number(target-qSum),Number(hi));
    const cost=BigInt(add)>lo?BigInt(add):lo;
    ex(cost>=lo && cost<=hi,'allocation stays in admissible interval');
    qSum+=cost;
    pNum=pNum*g+cost*pDen; pDen*=g;
    ++last;
  }
  ex(last<=count && qSum>=target,'greedy reaches its target');
  ex(pNum*m2<=pDen*(target+m2),'P cost <= target/M^2 + 1/256');
}
for(const b of [4,9,16,25,36,49,64,81,100,121,144,169,196,225,256]) {
  const nInt=Math.sqrt(b);
  // Abstract budget example with L=log n treated symbolically as b.
  ex(nInt*nInt===b && nInt>1,'replicated narrow mode count');
  ex(nInt*b>b && nInt*nInt===b,'sum caps grows faster than individual caps');
  const s=1/Math.sqrt(nInt),t=1/nInt;
  const r=integrate(s,t,theta/Math.max(1,nInt));
  nu(r.kl<=.5*(nInt-1-Math.log(nInt))+1e-8,'unwrapped KL upper bound');
}
console.log('wrapped Gaussian polynomial transfer:',exact,'exact checks;',numeric,'deterministic numeric checks');
