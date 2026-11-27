"use strict";
// Exact finite checks of trace identities and dual-kernel phases.
let checks=0;
function eq(x,y,what){checks++;if(x!==y)throw Error(what+": "+x+" !== "+y);}
const mod=(x,n)=>((x%n)+n)%n;
function reduceRoots(exps,p,b){
  const m=p**(b-1),n=(p-1)*m;
  const a=Array(n).fill(0);
  for(let k of exps){
    k=mod(k,p*m);
    if(k<n){a[k]++;continue;}
    for(let i=0;i<p-1;i++)a[k-n+i*m]--;
  }
  return a;
}
function powerTrace(p,b,j){
  const m=p**(b-1),n=(p-1)*m;let tr=0;
  for(let l=0;l<n;l++)tr+=reduceRoots([j+l],p,b)[l];
  return tr;
}
function gcd(a,b){return b===0?Math.abs(a):gcd(b,a%b);}
for(const p of [2,3,5,7,11])for(let b=1;b<=3;b++){
  if(p**b>120)continue;
  const m=p**(b-1),n=(p-1)*m;
  let d=0;
  for(let j=0;j<2*p*m;j++){
    const actual=powerTrace(p,b,j);
    eq(actual,m*((j%(p*m)===0?p:0)-(j%m===0?1:0)),"Ramanujan trace");
    if(j<n)d=gcd(d,actual);
  }
  eq(d,m,"trace image generator");
  for(let a=1;a<=b;a++){
    const delta=p**(b-a),stride=p**a;
    for(let j=0;j<delta;j++){
      const exp=Array.from({length:delta},(_,k)=>j*(1+k*stride));
      const answer=reduceRoots(exp,p,b);
      eq(answer[0],j===0?delta:0,"relative trace constant coefficient");
      eq(answer.slice(1).every(c=>c===0),true,"relative trace other coefficients");
    }
  }
}
function allInt(n,lo,hi,visit){
  const z=Array(n).fill(0);
  function loop(i){if(i===n){visit(z);return;}
    for(let x=lo;x<=hi;x++){z[i]=x;loop(i+1);}}
  loop(0);
}
for(const p of [3,5,7,11]){
  const M=p-1;
  // Each root kernel twist has finite phase denominator M; test the listed shell
  // against bounded integer offsets and independent exact phase counts.
  let best=Infinity;const phases=new Map();
  allInt(M,0,2,z=>{
    if(Math.min(...z)!==0 || Math.max(...z)===0)return;
    const sum=z.reduce((x,y)=>x+y,0), norm=M*z.reduce((x,y)=>x+y*y,0)-sum*sum;
    if(norm<best){best=norm;phases.clear();}
    if(norm===best){
      const t=mod(sum-M*z[0],M);
      phases.set(t,(phases.get(t)||0)+1);
    }
  });
  eq(best,M-1,"shortest dual numerator");
  eq([...phases.values()].reduce((x,y)=>x+y,0),p===3?2:2*M,"shortest dual multiplicity");
  eq([...phases.keys()].every(t=>t===1||t===M-1),true,"nontrivial first-shell characters");
  eq(phases.get(1),p===3?2:M,"symmetry of first-shell phases");
  if(p<=7)allInt(p,-1,1,z=>{
    const sum=z.reduce((a,b)=>a+b,0);
    const J=p*z[0]-sum;
    if(J===0)eq(z.slice(1).reduce((a,b)=>a+b-z[0],0),0,"integral root kernel");
    // Multiply by M: remainder coordinates in the subspace perpendicular to P e0.
    const numer=z.slice(1).map(x=>M*x-(sum-z[0]));
    const t=numer[0];
    eq(mod(t,M),mod(J,M),"cyclic phase equals trace label");
  });
}
console.log("OK: "+checks+" exact trace, kernel and character checks.");
