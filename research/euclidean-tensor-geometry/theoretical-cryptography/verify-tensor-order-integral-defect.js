"use strict";
// Exact finite checks for the character-block and wild-matrix calculations.
let checks=0;
function eq(x,y,msg){checks++;if(x!==y)throw Error(msg+": "+x+" !== "+y);}
const gcd=(a,b)=>b===0?Math.abs(a):gcd(b,a%b);
const lcm=(a,b)=>a/gcd(a,b)*b;
const mod=(x,p)=>((x%p)+p)%p;
function pow(a,k,p){let v=1;for(;k;k=Math.floor(k/2),a=mod(a*a,p))
  if(k%2)v=mod(v*a,p);return v;}
function all(shape){
  let result=[[]];
  for(const n of shape)result=result.flatMap(prefix=>Array.from({length:n},(_,i)=>[...prefix,i]));
  return result;
}
function identityCounts(p,e0,E){
  const g=Array.from({length:p-2},(_,i)=>i+2)
    .find(x=>new Set(Array.from({length:p-1},(_,k)=>pow(x,k,p))).size===p-1);
  eq(Boolean(g),true,"primitive residue-field root");
  const ell=E.map(e=>e/gcd(e,e0)).reduce(lcm,1);
  const shape=all(E),D=shape.length/ell;
  const w=E.map(e=>e0*ell/e);
  const key=h=>h.join(",");
  const reps=new Map();
  for(const h of shape){
    const orbit=Array.from({length:ell},(_,z)=>h.map((v,i)=>mod(v+z*e0,E[i])));
    eq(new Set(orbit.map(key)).size,ell,"orbit action free");
    const k=orbit.map(key).sort()[0];
    if(!reps.has(k))reps.set(k,h);
  }
  eq(reps.size,D,"number of normalization components");
  const rows=[...reps.values()];
  const groups=Array.from({length:ell},()=>[]);
  const exact=[],viaV=[];
  const den=[e0,...E].reduce(lcm,1);
  for(const a of shape){
    const T=a.reduce((s,v,i)=>s+v*w[i],0),r=T%ell,s=Math.floor(T/ell);
    groups[r].push(a);
    for(let b=0;b<e0;b++){
      exact.push(Math.floor((b*(den/e0)+a.reduce((x,y,i)=>x+y*(den/E[i]),0))/den));
      viaV.push(Math.max(0,Math.ceil((s-b)/e0)));
    }
  }
  eq(exact.sort((x,y)=>x-y).join(","),viaV.sort((x,y)=>x-y).join(","),"relative DVR exponents descend");
  for(const A of groups){
    eq(A.length,D,"weight fiber size");
    // Character inner products kill every nontrivial quotient character.
    for(let i=0;i<D;i++)for(let j=0;j<D;j++){
      const integral=rows.reduce((total,h)=>total+pow(g,mod(
        h.reduce((x,y,k)=>x+y*(A[i][k]-A[j][k])*((p-1)/E[k]),0),p-1),p),0);
      eq(mod(integral,p),i===j?D%p:0,"quotient character-table invertibility");
    }
  }
}
for(const [p,e0,E] of [
  [5,1,[1,2,4]],[7,1,[2,3,6]],[13,1,[2,3,4,6]],[17,1,[2,2,2,2,2]],
  [5,5,[2,4]],[5,10,[2,4]],[7,7,[1,2,3,6]],[7,21,[2,3,6]],[13,52,[2,3,4,6]]
])identityCounts(p,e0,E);
for(let e=1;e<=20;e++)for(let f=1;f<=20;f++){
  const count=all([e,f]).filter(([i,j])=>i*f+j*e>=e*f).length;
  eq(count,(e*f-e-f+gcd(e,f))/2,"two-factor carry count");
}
for(let t=1;t<=9;t++){
  const H=Array(t).fill(2);const c=Array(t).fill(0);
  for(const a of all(H)) c[Math.floor(a.reduce((x,y)=>x+y,0)/2)]++;
  const target=Array(t).fill(0);let b=1;
  for(let j=0;j<=t;j++){target[Math.floor(j/2)]+=b;b=b*(t-j)/(j+1);}
  eq(c.join(","),target.join(","),"multiquadratic exponents");
}
// Smith exponents from determinantal divisors of the exact basis matrices.
function sub(n,k){
  let result=[];
  function go(start,A){
    if(A.length===k){result.push(A);return;}
    for(let i=start;i<n;i++)go(i+1,[...A,i]);
  }
  go(0,[]);return result;
}
function det(M){
  if(M.length===0)return 1;
  return M[0].reduce((s,x,i)=>s+(-1)**i*x*det(M.slice(1).map(r=>r.filter((y,j)=>j!==i))),0);
}
function smith(M){
  const n=M.length, res=[];let last=1;
  for(let k=1;k<=n;k++){
    const X=sub(n,k);let d=0;
    for(const i of X)for(const j of X)d=gcd(d,det(i.map(r=>j.map(s=>M[r][s]))));
    res.push(d/last);last=d;
  }
  return res;
}
const m1=[[1,0,0,0],[0,0,1,1],[0,1,0,0],[0,0,-1,1]];
const m2=[[1,0,0,-2],[0,1,-1,0],[0,0,0,4],[0,0,2,0]];
eq(smith(m1).join(","),"1,1,1,2","first wild tensor basis");
eq(smith(m2).join(","),"1,1,2,4","second wild tensor basis");
console.log("OK: "+checks+" exact character, exponent and basis-matrix checks.");
