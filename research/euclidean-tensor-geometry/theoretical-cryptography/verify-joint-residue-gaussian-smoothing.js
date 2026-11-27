"use strict";
// Exact formal-Fourier arithmetic and scalar checks, plus numerical density
// sanity checks. Generated toy inputs only; no cryptographic transcripts.
let exact=0, numeric=0;
function check(p, message, isNumeric=false) {
  if (!p) throw Error(message);
  if (isNumeric) ++numeric; else ++exact;
}
const mod=(a,n)=>(a%n+n)%n;
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a;}
function Q(n,d=1n){
  n=BigInt(n);d=BigInt(d);
  const g=gcd(n,d)*(d<0n?-1n:1n);
  return [n/g,d/g];
}
const add=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const neg=a=>[-a[0],a[1]];
const sub=(a,b)=>add(a,neg(b));
const mul=(a,b)=>Q(a[0]*b[0],a[1]*b[1]);
const div=(a,b)=>Q(a[0]*b[1],a[1]*b[0]);
const sq=a=>mul(a,a);
const qp=(a,k)=>Q(a[0]**BigInt(k),a[1]**BigInt(k));
const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
const zero=()=>Array.from({length:8},()=>Q(0));
const rz=Array.from({length:24},(_,k)=>{
  const p=Array(24).fill(0n);p[k]=1n;
  // cyclotomic relation zeta_24^8 = zeta_24^4 - 1
  for(let i=23;i>=8;--i){p[i-4]+=p[i];p[i-8]-=p[i];}
  return p.slice(0,8).map(a=>Q(a));
});
const root=k=>rz[mod(k,24)];
const pa=(a,b)=>a.map((x,i)=>add(x,b[i]));
const ps=(a,b)=>a.map((x,i)=>sub(x,b[i]));
const pc=(a,s)=>a.map(x=>mul(x,s));
const pe=(a,b)=>a.every((x,i)=>eq(x,b[i]));
const pm=(a,b)=>{
  let out=zero();
  for(let i=0;i<8;++i)for(let j=0;j<8;++j)
    out=pa(out,pc(root(i+j),mul(a[i],b[j])));
  return out;
};
const cos=k=>pc(pa(root(k),root(-k)),Q(1,2));
const one=root(0);
// Given abstract Gaussian Fourier moments p^(k^2), average finite labels by
// summing roots rather than using the indicator formulas in the note.
for(const q of [1,2,3,4,6,8,12,24]){
  for(let k=-49;k<=49;++k){
    let avg=zero();
    for(let j=0;j<q;++j)avg=pa(avg,root(24/q*j*k));
    avg=pc(avg,Q(1,q));
    check(pe(avg,k%q===0?one:zero()),"character selection");
  }
  for(const p of [Q(1,13),Q(4,7),Q(6,7),Q(999,1000),Q(1)]){
    for(let t=0;t<24;++t){
      const parts=[[-1,Q(1,2)],[1,Q(1,2)]];
      let first=zero(), second=zero();
      for(let j=0;j<q;++j){
        const off=-(t+(24/q)*j);
        for(const [k,w] of parts){
          first=pa(first,pc(root(k*off),mul(w,div(qp(p,k*k),Q(q)))));
          for(const [l,w2] of parts){
            const f=k+l;
            second=pa(second,pc(root(f*off),mul(mul(w,w2),div(qp(p,f*f),Q(q)))));
          }
        }
      }
      const variance=ps(second,pm(first,first));
      const base=q<=2?pc(pa(one,pc(cos(2*t),qp(p,4))),Q(1,2)):pc(one,Q(1,2));
      const m=q===1?pc(cos(t),p):zero();
      check(pe(first,m),"first phase moment");
      check(pe(variance,ps(base,pm(m,m))),"first harmonic variance");
    }
  }
}
for(let ar=1;ar<=9;++ar)for(let br=1;br<=8;++br)
for(let xr=-7;xr<=7;++xr)for(let yr=-6;yr<=6;++yr){
  const a=Q(ar,5),b=Q(br,7), x=Q(xr,3),y=Q(yr,4),s=add(a,b);
  const c=div(mul(a,b),s),t=div(a,s),d=sub(a,c);
  check(eq(d,mul(s,sq(t))),"posterior-mean variance");
  const left=add(div(sq(x),a),div(sq(sub(y,x)),b));
  const right=add(div(sq(y),s),div(sq(sub(x,mul(t,y))),c));
  check(eq(left,right),"completed square");
}
const phi=(a,x)=>Math.exp(-Math.PI*x*x/a)/Math.sqrt(a);
function theta(a,t){
  let s=1;
  for(let k=1;k<=20;++k)s+=2*Math.exp(-Math.PI*a*k*k)*Math.cos(2*Math.PI*k*t);
  return s;
}
for(const q of [1,2,3,5,8])
for(const t of [0,1/9,1/4,1/2])
for(const a of [0.72,1.9,3.6])
for(const b of [0.31,2,32])
for(const y of [-1.2,-0.07,0,0.48,1.63]){
  let den=0;
  for(let j=-240;j<=240;++j)den+=phi(a,t+j/q);
  for(let j=0;j<q;++j){
    const z=t+j/q;
    let num=0;
    for(let k=-28;k<=28;++k)
      num+=phi(a,z+k)*phi(b,y-z-k);
    const actual=q*num/(den*phi(a+b,y));
    const predicted=theta(a*b/(a+b),a*y/(a+b)-z)/theta(q*q*a,q*t);
    check(Math.abs(actual-predicted)<8e-12,"joint likelihood against direct densities",true);
  }
}
console.log("Joint Gaussian-residue smoothing: "+exact+" exact checks and "+numeric+" floating checks passed.");
