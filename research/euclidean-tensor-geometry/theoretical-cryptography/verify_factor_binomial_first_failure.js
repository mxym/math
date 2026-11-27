"use strict";

// Finite exact checks for balanced binomial first-failure identities.
// Run: node verify_factor_binomial_first_failure.js
const ps=[];
for(let p=2;p<=2400;++p)if(!ps.some(q=>q*q<=p&&p%q===0))ps.push(p);
const fl=(a,p)=>Math.floor(a/p);
function vf(n,p){let v=0;while(n>=p){n=fl(n,p);v+=n;}return v;}
function vp(n,p){let v=0;while(n%p===0){++v;n/=p;}return v;}
function add(n,k,p){
  let c=0,count=0;
  while(n||k) {
    c=+(n%p+k%p+c>=p);count+=c;
    n=fl(n,p);k=fl(k,p);
  }
  return count;
}
function predicted(m,p,v){
  const h=vp(m,p)+v+1,q=p**h;
  if(!Number.isSafeInteger(q)) throw Error("fixture exceeded exact integer range");
  return q-m%q;
}
let checks=0,pairs=0,conditional=0,global=0,positiveOnly=0;
const check=(b,label)=>{++checks;if(!b) throw Error(label);};
for(let m=1;m<=420;++m)for(const p of ps){
  if(p>130)break;
  const V=vf(2*m,p)-2*vf(m,p);
  check(V===add(m,m,p),"central Legendre against Kummer");
  for(let v=0;v<=Math.min(5,V+1);++v) {
    const b=predicted(m,p,v);
    check(vf(m+b,p)-vf(b,p)-vf(m,p)>=v+1,"first-hit attainable");
    for(let k=1;k<Math.min(b,100);++k)
      check(vf(m+k,p)-vf(k,p)-vf(m,p)<=v,"bounded exhaustive necessity");
    for(let k=Math.max(1,b-5);k<b;++k)
      check(vf(m+k,p)-vf(k,p)-vf(m,p)<=v,"immediate necessity");
    ++pairs;
  }
  if(predicted(m,p,V)<=50)
    check(p<=2*predicted(m,p,V),"large-prime necessary cutoff");
}
for(let m=1;m<=154;++m){
  // For these fixtures direct integer coefficient comparison gives B <= 3m,
  // so no p>m+3m can divide the binomial at a competing onset.
  let C=1n;
  for(let j=1;j<=m;++j) C=C*BigInt(m+j)/BigInt(j);
  let left=1n,B=0;
  for(let k=1;k<=3*m;++k) {
    left=left*BigInt(m+k)/BigInt(k);
    if(C%left!==0n){B=k;break;}
  }
  check(B>0,"global fixture first failure found");
  let pred=Infinity,missing=Infinity;
  for(const p of ps) {
    if(p>m+3*m)break;
    const V=vf(2*m,p)-2*vf(m,p);
    const b=predicted(m,p,V);
    pred=Math.min(pred,b);
    if(V===0)missing=Math.min(missing,b);
  }
  check(pred===B,"global nearest-multiple formula");
  if(missing>B)++positiveOnly;
  ++global;
}
// Conditional residue counting inside a single base. Fixing the two low
// digits in [-K,-1] modulo p^2 leaves each higher digit free before imposing
// the high-digit inequality, exactly as in the proof.
for(const p of [2,3,5,7,11,13]) for(let d=3;d<=5;++d)
for(const K of [1,p-1,p+1,2*p-1]){
  if(K>=p*p)continue;
  const non=p-Math.floor(p/2), high=p-non;
  let sum=0,counts=0;
  for(let a=p*p-K;a<p*p;++a)for(let n=a;n<p**d;n+=p*p) {
    let z=fl(n,p*p),head=0;
    for(let j=2;j<d;++j){head+=+(z%p>=Math.ceil(p/2));z=fl(z,p);}
    sum+=+(head<=1);
    counts+=+(add(n,n,p)<=1);
  }
  check(sum===K*(non**(d-2)+(d-2)*high*non**(d-3)),
    "conditional high-digit formula");
  check(counts<=sum&&counts<=K*(d-1)*non**(d-2),"conditional carry upper bound");
  ++conditional;
}
console.log("PASS: "+checks+" exact assertions, "+pairs+" prime-threshold fixtures, "
  +global+" global binomial comparisons, "+conditional+" conditional digit fixtures");
console.log(positiveOnly+" of the global small fixtures first fail only at positive valuation");
