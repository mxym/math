"use strict";
// Deterministic abstract/no-input checks for integer energy shell identities.
let exact=0, numerical=0;
function check(ok,msg,isExact=true) {
  if(!ok) throw new Error(msg);
  if(isExact)++exact;else++numerical;
}
const cap=128, rows=31, R=Array.from({length:rows},()=>Array(cap+1).fill(0n));
R[0][0]=1n;
for(let m=1;m<rows;++m) for(let e=0;e<=cap;++e) {
  R[m][e]=R[m-1][e];
  for(let j=1;j*j<=e;++j) R[m][e]+=2n*R[m-1][e-j*j];
}
for(let e=1;e<=cap;++e) {
  let s=0n;
  for(let d=1;d<=e;++d) if(e%d===0) s+=((e+d)%2 ? -1n:1n)*BigInt(d)**3n;
  check(R[8][e]===16n*s,"eight-square divisor formula");
}
function choose(n,k) {
  if(k<0 || k>n)return 0n;
  let out=1n;
  for(let j=1;j<=k;++j) out=out*BigInt(n+1-j)/BigInt(j);
  return out;
}
for(let n=4;n<rows;++n) for(let k=0;k<=n;++k) for(let e=0;e<=cap;++e) {
  let s=0n;
  for(let j=0;j<=e;++j) s+=R[k][j]*R[n-k][e-j];
  check(s===R[n][e],"shell likelihood normalization");
  if(e<=3) for(let j=0;j<=e;++j) {
    check(R[k][j]*R[n-k][e-j]===2n**BigInt(e)*choose(k,j)*choose(n-k,e-j),
      "unsigned support count on a small energy shell");
  }
}

const {exp, sin, cos, sqrt, PI, abs, floor, min,max, log}=Math;
const phi=z=>exp(-z*z/2)/sqrt(2*PI);
function local(t) {
  const terms=[[0,1]];
  let z=1,M=0,M2=0,M3=0;
  for(let j=1;;++j) {
    const a=j*j, w=2*exp(-t*a);
    if(w<1e-23)break;
    terms.push([a,w]);z+=w;M+=w*a;M2+=w*a*a;M3+=w*a*a*a;
  }
  M/=z;M2/=z;M3/=z;
  const sd=sqrt(M2-M*M);
  const g=(M3-3*M*M2+2*M**3)/sd**3;
  return {M,sd,g,terms:terms.map(([i,w])=>[i,w/z])};
}
function match(r) {
  let lo=min(.01,.01/r),hi=40;
  for(let j=0;j<65;++j) {
    const m=(lo+hi)/2;
    if(local(m).M>r)lo=m;else hi=m;
  }
  return (lo+hi)/2;
}
function laws(t,n,cut,saves) {
  const {terms}=local(t), out=new Map();
  let P=new Float64Array(cut+1); P[0]=1;
  if(saves.includes(0))out.set(0,P);
  for(let m=1;m<=n;++m) {
    const Q=new Float64Array(cut+1);
    for(const [a,w] of terms) for(let j=a;j<=cut;++j) Q[j]+=w*P[j-a];
    P=Q;
    if(saves.includes(m))out.set(m,P);
  }
  return out;
}
function normalTV(a,h=0) {
  const s=sqrt(1-a);let integral=0;
  for(let j=0;j<16000;++j) {
    const z=-12+(j+.5)*.0015;
    integral+=abs(phi(z/s)/s-phi(z+h));
  }
  return integral*.0015/2;
}
function shellTV(t,n,k,e,p,retuned=p.get(k)) {
  const factor=p.get(n)[e], q=p.get(n-k), pk=p.get(k);
  let sum=0,diff=0,mass=0;
  for(let j=0;j<=e;++j) {
    const a=pk[j]*q[e-j]/factor,b=retuned[j];
    sum+=b;mass+=a;diff+=abs(a-b);
  }
  check(abs(mass-1)<3e-12,"shell mass numerical normalization",false);
  return (diff+1-sum)/2;
}
for(const [n,e] of [[240,9600],[280,700],[600,600],[4096,120],[12000,90]]) {
  const ra=e/n,t=match(ra),loc=local(t),M=min(n,e);
  check(abs(loc.M/ra-1)<2e-13,"moment matching",false);
  const k=floor(.42*n), a=k/n, p=laws(t,n,e,[k,n-k,n]);
  const target=normalTV(a);
  const dis=shellTV(t,n,k,e,p);
  check(abs(dis-target)<.42/sqrt(M),"fixed-fraction TV "+[n,e,dis,target],false);
  for(const m of [k,n-k,n]) for(let j=0;j<=e;++j) {
    const z=(j-m*ra)/(loc.sd*sqrt(m));
    const pred=phi(z)*(1+loc.g*(z**3-3*z)/(6*sqrt(m)));
    const observed=loc.sd*sqrt(m)*p.get(m)[j];
    check(abs(observed-pred)<.8/(m*min(1,ra)),"local Edgeworth "+[n,e,m,j,observed,pred],false);
  }
  if(e<1000) for(const h of [-1.2,1.2]) {
    const s=t+h/(loc.sd*sqrt(k));
    const shifted=laws(s,k,e,[k]).get(k), d=shellTV(t,n,k,e,p,shifted);
    check(d>dis+.1,"scale retuning increases distance",false);
    check(abs(d-normalTV(a,h))<2.5/sqrt(M),"retuning profile",false);
  }
}
for(const [n,e,k] of [[1024,920,80],[1800,540,120],[2400,720,120]]) {
  const t=match(e/n),p=laws(t,n,e,[n,n-k,k]),d=shellTV(t,n,k,e,p);
  check(abs(d/(phi(1)*k/n)-1)<.16,"small fraction TV scale "+[n,e,k,d],false);
}
function fixedTV(e,a) {
  let p=exp(-a*e),tot=0,d=0;
  for(let j=0;j<=e;++j) {
    const b=Number(choose(e,j))*a**j*(1-a)**(e-j);
    tot+=p;d+=abs(p-b);p*=a*e/(j+1);
  }
  return (d+1-tot)/2;
}
for(const e of [1,2,3,4,7,9]) for(const frac of [.05,.3,.72,1]) {
  const n=769,k=floor(n*frac),t=match(e/n),p=laws(t,n,e,[n,k,n-k]);
  const d=shellTV(t,n,k,e,p);
  check(abs(d-fixedTV(e,k/n))<e*e/n,"bounded-energy law",false);
}
for(const t of [1e-7,1e-5,.001,.017,.18,1]) {
  const {terms}=local(t);
  const grid=[.5*t,.9*t,3*t,9*t,PI/2,PI/3,PI/4,2*PI/3,PI,.999*PI];
  for(let b=1;b<300;++b) grid.push(PI*b/300);
  for(const v of grid) if(v>=.5*t && v<=PI) {
    let re=0,im=0;
    for(const [j,w] of terms){ re+=w*cos(v*j); im+=w*sin(v*j); }
    check(re*re+im*im<.99*.99,"generated theta outer characteristic gap "+[t,v,re,im],false);
  }
}
console.log(JSON.stringify({exact,numerical}));
