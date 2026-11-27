/* Node 18+. Standalone synthetic probability and arithmetic checks. */
'use strict';
let exact=0,numeric=0;
function ex(q,msg) { ++exact; if(!q) throw Error(msg); }
function nu(q,msg) { ++numeric; if(!q) throw Error(msg); }
function gammaMoment(r,j) {
  let x=1n;
  for(let k=0;k<j;++k) x*=r+BigInt(k);
  return x;
}
for(let r=1n;r<=1000n;++r) {
  const a=[0,1,2,3,4,5,6].map(j=>gammaMoment(r,j));
  const mean=a[2]-2n*a[1]+r;
  const v=a[4]-4n*a[3]+4n*a[2]-(a[2]-2n*a[1])**2n;
  ex(mean===r*r,'gamma energy-square mean');
  ex(v===4n*r**3n+2n*r*r+2n*r,'gamma energy-square variance');
  const e4=a[4]-4n*r*a[3]+6n*r*r*a[2]-4n*r**3n*a[1]+r**4n;
  ex(e4===3n*r*r+6n*r,'complex standard radial centered fourth moment');
  for(const m of [1n,2n,7n,32n,100n,127n,2026n]) {
    ex(m*v+4n*m*(m-1n)/2n*r*r===m*(v+2n*(m-1n)*r*r),'variance pair coefficient');
  }
}
/*
 A finite moment proxy for a standard complex normal at orders (1,1),(2,2).
 A coordinate equals sqrt(2) times 1,-1,i,-i, each with weight 1/8,
 or zero with weight 4/8. Its first two complex mixed moments match.
 The quadratic form scores on a Hermitian basis are integral.
*/
const z=[[0,0,4], [1,0,1],[-1,0,1],[0,1,1],[0,-1,1]];
for(let r=1;r<=5;++r) {
  const d=r*r,cov=Array.from({length:d},()=>Array(d).fill(0n)),mu=Array(d).fill(0n);
  let wsum=0n;
  function run(arr, wt) {
    if(arr.length<r) {for(const e of z) run([...arr,e],wt*BigInt(e[2]));return;}
    const s=arr.map(([x,y])=>2*(x*x+y*y)-1);
    for(let i=0;i<r;++i) for(let j=i+1;j<r;++j) {
      const [a,b]=arr[i], [c,d]=arr[j];
      s.push(4*(a*c+b*d),4*(b*c-a*d));
    }
    for(let i=0;i<d;++i) {
      mu[i]+=wt*BigInt(s[i]);
      for(let j=0;j<d;++j) cov[i][j]+=wt*BigInt(s[i]*s[j]);
    }
    wsum+=wt;
  }
  run([],1n); ex(wsum===8n**BigInt(r),'proxy mass');
  for(let i=0;i<d;++i) {
    ex(mu[i]===0n,'proxy centered score');
    for(let j=0;j<d;++j) ex(cov[i][j]===(i===j?wsum*(i<r?1n:2n):0n),'Hermitian score covariance');
  }
}
for(let q=2n;q<=384n;++q) for(let k=1n;k<q;++k) {
  const a=q+k, b=q-k;
  ex(q*q-k*k===a*b,'complex scalar second moment denominator');
  ex(a*(2n*q-a)===a*b,'Gaussian integral beta=2 normalization');
}
for(let D=2;D<=64;D*=2){
  for(let a=0;a<D;++a) for(let b=0;b<D;++b) {
    let sum=0;
    for(let j=0;j<D/2;++j) sum+=Math.cos(Math.PI*(2*j+1)*(a-b)/D)/D;
    nu(Math.abs(sum-(a===b?.5:0))<3e-14,'dyadic real-isometry coefficients');
  }
}
// Reproducible simulation, used only to illustrate the TV limit on scalar blocks.
let seed=0x3e241f08;
function rng() {
  seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;
  return ((seed>>>0)+.5)/4294967296;
}
function stdNormal() {return Math.sqrt(-2*Math.log(rng()))*Math.cos(2*Math.PI*rng());}
function gamma(shape) {
  const d=shape-1/3,c=1/Math.sqrt(9*d);
  for(;;) {
    const x=stdNormal(), z=1+c*x;
    if(z<=0)continue;
    const z3=z*z*z,u=rng();
    if(u<1-.0331*x**4 || Math.log(u)<.5*x*x+d*(1-z3+Math.log(z3))) return d*z3;
  }
}
function phi(x) {
  const t=1/(1+.2316419*Math.abs(x));
  const p=Math.exp(-x*x/2)/Math.sqrt(2*Math.PI)*
    t*(.319381530+t*(-.356563782+t*(1.781477937+t*(-1.821255978+t*1.330274429))));
  return x>=0?1-p:p;
}
for(const p of [24,96,384]) for(const v of [.08,.25,1,4]) {
  const m=Math.round(p/v),k=10000;
  let sum=0,square=0;
  for(let rep=0;rep<k;++rep) {
    let L=0;
    for(let i=0;i<p;++i) {
      const e=gamma(m)/m-1;
      L+=-Math.log1p(e)-Math.log(rng())*e/(1+e);
    }
    const tv=L<0?-Math.expm1(L):0;
    nu(tv>=0 && tv<=1,'overlap contribution');
    sum+=tv;square+=tv*tv;
  }
  const avg=sum/k,se=Math.sqrt((square/k-avg*avg)/k), limiting=2*phi(Math.sqrt(v)/2)-1;
  nu(Math.abs(avg-limiting)<5*se+.095/Math.sqrt(p),'scalar TV profile cross-check');
  console.log('p',p,'m',m,'simulated TV',avg.toFixed(5),'limit',limiting.toFixed(5));
}
console.log('labeled Gaussian covariance:', exact, 'exact checks;', numeric, 'deterministic numeric checks');
