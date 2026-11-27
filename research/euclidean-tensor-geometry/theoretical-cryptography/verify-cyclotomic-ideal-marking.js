"use strict";
// Standalone exact checks, using only generated cyclotomic orders.
let exact=0;
function check(ok,msg){if(!ok) throw new Error(msg);++exact;}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a;}
function lcm(a,b){return a/gcd(a,b)*b;}
function factors(n){
  const f=[];
  for(let p=2;p*p<=n;++p)if(n%p===0){
    let e=0;while(n%p===0){n/=p;++e;} f.push([p,e]);
  }
  if(n>1)f.push([n,1]);return f;
}
function phi(n){return factors(n).reduce((r,[p])=>r/p*(p-1),n);}
function ramanujan(w,k){
  let value=1;
  for(const [p,e] of factors(w)){
    const t=p**(e-1);
    if(k%t) return 0;
    value*=k%(p*t)?-t:t*(p-1);
  }
  return value;
}
function reps(m) {
  const w=m%2?2*m:m, n=phi(m);
  let v=[{i:0,r:[],x:[]}], pset=[],size=1;
  for(const [p,e] of factors(m)) {
    const primePower=p**e, base=p**(e-1), tmp=[];
    size*=base;if(p>2)pset.push(p);
    for(const old of v) for(let r=0;r<base;++r)
      for(let x=0;x<(p===2?1:p);++x)
        tmp.push({i:(old.i+(r+base*x)*(w/primePower))%w,r:[...old.r,r],x:p===2?old.x:[...old.x,x]});
    v=tmp;
  }
  const d=pset.reduce((a,p)=>a*p,1);
  return {w,n,v,pset,b:size,d};
}
const orders=[...Array.from({length:120},(_,i)=>i+1).filter(x=>x%4!==2),135,147,180,210,225,273,315,420];
for(const m of orders){
  const {w,n,v,pset,b,d}=reps(m);
  check(n===b*phi(d)&&2*b*d===w&&v.length===w/2,"rank and minimum shell size");
  check(new Set(v.map(x=>x.i%(w/2))).size===v.length,"one line representative per pair");
  check(n===phi(w),"normalization of maximal root order");
  for(const x of v)for(const y of v){
    let value=x.r.every((a,i)=>a===y.r[i])?n:0;
    if(value) for(let j=0;j<pset.length;++j)if(x.x[j]!==y.x[j])value/=1-pset[j];
    const raw=ramanujan(w,x.i-y.i);
    check(value===raw,"shortest weighted Gram "+[m,x.i,y.i,value,raw]);
  }
}
function factorial(n){let r=1n;for(let i=2;i<=n;++i)r*=BigInt(i);return r;}
function countAutomorphisms(M){
  const n=M.length,P=Array(n).fill(-1),used=Array(n).fill(false);
  let total=0n;
  function visit(l){
    if(l===n){++total;return;}
    for(let v=0;v<n;++v)if(!used[v]){
      let ok=true;
      for(let k=0;k<l;++k)if(M[k][l]!==M[P[k]][v]){ok=false;break;}
      if(!ok)continue;
      P[l]=v;used[v]=true;visit(l+1);used[v]=false;
    }
  }
  visit(0);return total;
}
for(const m of [1,3,4,5,7,8,9,12,15,16,20,24]){
  const {w,n,v,pset,b}=reps(m);
  const M=v.map(x=>v.map(y=>Math.abs(ramanujan(w,x.i-y.i))));
  const observed=countAutomorphisms(M)*2n**BigInt(b);
  const expected=(2n*pset.reduce((x,p)=>x*factorial(p),1n))**BigInt(b)*factorial(b);
  check(observed===expected,"exhaustive weighted shell isometry count "+m);
  const affine=new Set();
  for(let a=0;a<w;++a)for(let j=1;j<=w;++j)if(gcd(j,w)===1)
    affine.add(Array.from({length:w},(_,i)=>(a+j*i)%w).join(","));
  check(affine.size===w*n,"multiplication normalizer count");
  check((observed===BigInt(affine.size))===[1,3,4].includes(m),"geometric and semilinear equality cases");
}
function partitions(x,lo=1) {
  if(x===0)return [[]];
  const a=[];
  for(let j=lo;j<=x;++j)for(const p of partitions(x-j,j))a.push([j,...p]);
  return a;
}
function verifySpectrum(b,pset,perms,sign){
  const u=perms.flat().reduce((v,l)=>lcm(v,l),2);
  let frequencies=[sign?u/2:0];
  for(const p of perms){
    let roots=p.flatMap(c=>Array.from({length:c},(_,j)=>u/c*j));roots.splice(roots.indexOf(0),1);
    frequencies=frequencies.flatMap(x=>roots.map(y=>(x+y)%u));
  }
  const w=2*b*pset.reduce((a,x)=>a*x,1), denom=u*b;
  const actual=frequencies.flatMap(x=>Array.from({length:b},(_,i)=>x+i*u));
  const q=denom/gcd(denom,actual[0]);
  const irreducible=actual.length===phi(q) && new Set(actual).size===actual.length
    && actual.every(x=>denom/gcd(denom,x)===q);
  const pred=perms.every(p=>p.length===1)&&(sign||b%2===1);
  check(irreducible===pred,"cycle type irreducibility "+[b,pset,JSON.stringify(perms),sign]);
  if(pred)check(q===(sign?w:w/2),"exact eigenvalue orders");
}
for(const m of orders){
  const {pset,b}=reps(m);
  if(pset.some(p=>p>7)||b>16)continue;
  function visit(l,perms){
    if(l===pset.length)for(const sign of [false,true])verifySpectrum(b,pset,perms,sign);
    else for(const p of partitions(pset[l]))visit(l+1,[...perms,p]);
  }
  visit(0,[]);
}
for(const m of orders) {
  const {w,n}=reps(m);
  for(let w0=2;w0<=w;w0+=2) if(w%w0===0 && phi(w0)===n)
    check(w0===w,"even root shell divisibility and degree recovery");
}
console.log(JSON.stringify({exact}));
