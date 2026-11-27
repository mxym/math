'use strict';
// Exact tests for FactorErdosStrausPrimePowerCoverage.md.
let numChecks=0;
function ck(p,why){if(!p)throw Error(why);++numChecks;}
const abs=a=>a<0n?-a:a;
function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a;}
const mod=(n,m)=>(n%m+m)%m;
function inv(a,n){
  let r=mod(a,n),oldr=n,s=1n,olds=0n;
  while(r){const q=oldr/r;[oldr,r]=[r,oldr-q*r];[olds,s]=[s,olds-q*s];}
  if(oldr!==1n)throw Error('inverse is undefined');
  return mod(olds,n);
}
function powmod(a,b,n){let r=1n;for(a=mod(a,n);b;b>>=1n,a=a*a%n)if(b&1n)r=r*a%n;return r;}
function isPrime(n){if(n<2)return false;if(n%2===0)return n===2;for(let p=3;p*p<=n;p+=2)if(n%p===0)return false;return true;}
function orbit(q,l){
  let a=1n,e=Infinity,m=Infinity,order=0;
  do {a=a*q%l;++order;
    if(e===Infinity && (4n*a+1n)%l===0n)e=order;
    if(m===Infinity && a===l-1n)m=order;
  } while(a!==1n);
  return {e,m,order,j:(e+1)/2};
}
function representI(n,c,d,f){
  const D=4n*c*d,L=4n*c*c*d+1n,k=L/f,a=(n+f)/D,b=a*k-c;
  ck(n>0n && (n+f)%D===0n && L%f===0n,'Type I integrality');
  const y=a*c*d,x=a*b*d,z=b*c*d*n;
  ck(y>0n && y<x && x<z,'Type I positivity and distinct denominators');
  ck(4n*x*y*z===n*(x*y+x*z+y*z),'Type I exact identity');
}
function representII(n,q,ell,m){
  const v=q**BigInt(m),c=(v+1n)/ell,d=(n+ell)/(4n*v);
  ck((v+1n)%ell===0n && (n+ell)%(4n*v)===0n,'Type II integrality');
  const x=v*d,y=c*d*n,z=v*c*d*n;
  ck(x>0n && x<y && y<z,'Type II positive distinct denominators');
  ck(4n*x*y*z===n*(x*y+x*z+y*z),'Type II exact identity');
}

const qp=Array.from({length:2500},(_,i)=>4*i+13).filter(isPrime).map(BigInt);
for(const ell of [3n,7n,11n,19n,23n,31n,43n,47n,59n]){
  for(const q of qp){
    if(q<=ell*ell)continue;
    const {e,m,order,j}=orbit(q%ell,ell);
    ck(e===Infinity || e%2===1,'least exponent parity');
    if(q%ell===mod(-4n,ell))ck(order%2===0 && e===order-1 && m===order/2 && m===j,'coincident exact depth');
    const expectedI=j===Infinity?Infinity:j,expectedAny=Math.min(j,m);
    let foundI=Infinity,foundII=Infinity;
    const last=Math.max(4,...[j,m].filter(Number.isFinite))+1;
    for(let i=1;i<=last;++i){
      const Q=q**BigInt(i),D=4n*Q,k0=inv(ell,D);
      let hitI=false,hitII=false,hitI4=false;
      for(let h=0;h<=i;++h){
        const c=q**BigInt(h),L=4n*Q*c+1n;
        // If f is not the least positive allowed witness, its cofactor is
        // below D and must be k0. Check both possibilities by divisibility.
        const direct=L%ell===0n;
        const inverse=L%k0===0n && (L/k0)%D===ell;
        hitI=hitI||direct||inverse;
        if(inverse)ck(direct && (h===0 || L/k0===ell),'no additional first-family hit through inverse cofactor');
        if(h===i)ck(!direct&&!inverse,'sum-of-two-squares even exponent exclusion');
        const r=q**BigInt(Math.abs(2*h-i))+1n;
        hitII=hitII||r%ell===0n;
        hitI4=hitI4||r%k0===0n;
      }
      ck(!hitI4,'fourth Type I family has no hit');
      if(hitI && foundI===Infinity)foundI=i;
      if(hitII && foundII===Infinity)foundII=i;
    }
    ck(foundI===expectedI && foundII===m && Math.min(foundI,foundII)===expectedAny,'both exact first-depth formulas');
    if(j!==Infinity){
      const D=4n*q**BigInt(j);
      for(const t of [1n,2n,19n])representI(D*t-ell,q**BigInt(j-1),q,ell);
    }
    if(m!==Infinity){
      const D=4n*q**BigInt(m);
      for(const t of [1n,5n,23n])representII(D*t-ell,q,ell,m);
    }
  }
}

const q=409n,ell=11n,M=4n*q*q,period=210n*M;
ck(isPrime(Number(q)) && M===669124n && (4n*q**3n+1n)/ell===24879247n,'q=409 example data');
const olds=[1n,121n,169n,289n,361n,529n],news=[22081081n,102375961n,50184289n,130479169n,122449681n,10036849n];
for(let i=0;i<olds.length;++i){
  const n=news[i];
  ck(n%840n===olds[i] && n%M===M-ell && gcd(n,period)===1n && n<period,'six reduced CRT refinements');
  representI(n,q,q,ell);
}
function ds(num){
  const s=[];
  for(let f=1;f*f<=num;++f)if(num%f===0){
    s.push(f);
    if(f*f!==num)s.push(num/f);
  }
  return s;
}
const forbid=new Map();
for(let p=13;p<=36000;p+=4){
  if(!isPrime(p))continue;
  const n=4*p+1;
  const f=ds(n).filter(v=>v%4===3);
  const below=f.filter(v=>v*v<n);
  ck(f.length===2*below.length,'complementary divisors and no square midpoint');
  const residues=new Set(f.map(v=>Number(mod(-BigInt(v),BigInt(p)))));
  ck(residues.size===f.length && !residues.has(0),'distinct nonzero covered residues');
  for(const v of f){
    const P=BigInt(p),F=BigInt(v);
    ck(powmod(-F,(P-1n)/2n,P)===P-1n,'negative divisor is a nonresidue');
    representI(4n*P-F,1n,P,F);
  }
  if([17,29,41].includes(p))forbid.set(p,residues);
}
const qs=[17,29,41],prod=qs.reduce((a,b)=>a*b,1);
const expected=qs.reduce((s,p)=>s*(p-1-forbid.get(p).size),1);
for(const r of olds){
  let got=0;
  for(let t=0;t<prod;++t){
    const n=Number(r)+t*840;
    if(qs.every(p=>n%p!==0&&!forbid.get(p).has(n%p)))++got;
  }
  ck(got===expected,'CRT product count inside each of six original residue classes');
}
console.log('Exact assertions passed: '+numChecks);
