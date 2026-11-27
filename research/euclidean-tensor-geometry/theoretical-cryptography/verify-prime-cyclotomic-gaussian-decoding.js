"use strict";
// Integer/rational checks for the geometric assertions in
// prime-cyclotomic-gaussian-decoding.md. No asymptotic or cryptographic test.
let checks=0;
function eq(x,y,where) {
  checks++;
  if(x!==y) throw Error(where+": got "+String(x)+" expected "+String(y));
}
function indexSets(n) {
  return Array.from({length:(1<<n)-2},(_,k)=>{
    const m=k+1;
    return Array.from({length:n},(_,i)=>i).filter(i=>m&(1<<i));
  });
}
const sum=a=>a.reduce((x,y)=>x+y,0);
function allInt(n,lo,hi,cb) {
  const z=[];
  function visit(i) {
    if(i===n) { cb(z); return; }
    for(let a=lo;a<=hi;a++) { z[i]=a; visit(i+1); }
  }
  visit(0);
}
function testSets(m,sets,bound,maxSize=m.length-1) {
  return sets.every(s=>s.length>maxSize ||
    Math.abs(sum(s.map(i=>m[i])))<=bound(s.length));
}
for(let n=3;n<=6;n++) {
  const sets=indexSets(n);
  const vectors=[];
  allInt(n,0,2,z=>{
    if(Math.min(...z)===0 && Math.max(...z)>0) {
      const s=sum(z);
      vectors.push([z.slice(),n*sum(z.map(a=>a*a))-s*s]);
    }
  });
  const shortest=vectors.filter(([,e])=>e===n-1);
  eq(shortest.length,2*n,"shortest count");
  eq(vectors.every(([,e])=>e>=n-1),true,"minimum norm");
  eq(shortest.every(([z])=>Math.max(...z)===1 &&
    (sum(z)===1||sum(z)===n-1)),true,"shortest signs");
  allInt(n-1,-3,3,a=>{
    const m=[...a,-sum(a)]; // y=m/(2n)
    const viaSets=testSets(m,sets,j=>j*(n-j));
    const viaOffsets=vectors.every(([z,e])=>sum(z.map((b,i)=>b*m[i]))<=e);
    eq(viaSets,viaOffsets,"subset vs bounded lattice-offset constraints");
  });
}
for(let n=4;n<=36;n++) for(let k=2;k<=Math.floor(n/2);k++) {
  // Exact missing-layer witness using scale 4n(n-k) and both sign tests.
  const a=2*n-2*k+1;
  const m=Array.from({length:n},(_,i)=>i<k?a*(n-k):-a*k);
  eq(sum(m),0,"missing-layer point in zero-sum subspace");
  const sorted=m.slice().sort((x,y)=>y-x);
  for(let j=1;j<k;j++){
    const rhs=2*(n-k)*j*(n-j);
    eq(sum(sorted.slice(0,j))<rhs,true,"positive lower layers pass");
    eq(-sum(sorted.slice(-j))<rhs,true,"negative lower layers pass");
  }
  eq(sum(sorted.slice(0,k))>2*(n-k)*k*(n-k),true,"omitted layer fails");
}
for(let k=2;k<=9;k++) {
  const sets=indexSets(k);
  allInt(k<6?k:0,0,4,z=>{
    if(k>=6) return;
    for(const s of sets) {
      // n(d1-y_i)=z_i; rescale via m_i=2n y_i, even for local points.
      const n=2*k+3;
      const m=z.map(zi=>n-1-2*zi);
      eq(sum(s.map(i=>m[i]))<=s.length*(n-s.length),
         sum(s.map(i=>z[i]))>=s.length*(s.length-1)/2,"local deficit inequality");
      eq(sum(m)>k*(n-k),sum(z)<k*(k-1)/2,"full cluster violation");
    }
  });
  // Positive volume: all deficits z=(k-1)/2-1/4 have strict slack.
  const z4=2*k-3;
  for(let j=1;j<k;j++) eq(j*z4>2*j*(j-1),true,"strict interior");
  eq(k*z4<2*k*(k-1),true,"strict defect");
}

// Rational arithmetic for the B2 and B3 coefficients.
function gcd(a,b){a=a<0n?-a:a;return b===0n?a:gcd(b,a%b);}
function Q(a,b=1n){a=BigInt(a);b=BigInt(b);const d=gcd(a,b);return [a/d,b/d];}
function add([a,b],[c,d]){return Q(a*d+b*c,b*d);}
function mul([a,b],[c,d]){return Q(a*c,b*d);}
function pow(x,n){let a=Q(1);while(n--) a=mul(a,x);return a;}
function integ(ci,t){
  return ci.reduce((a,c,i)=>add(a,mul(mul(c,pow(t,i+1)),Q(1,i+1))),Q(0));
}
function coeff(q,r,why){eq(q.join("/"),r.join("/"),why);}
const vol2=integ([Q(1),Q(-1)],Q(1));  // y>=0, x+y<1
const one=integ([Q(0),Q(3),Q(-1)],Q(1));
const two=integ([Q(1),Q(-2),Q(1)],Q(1));
const clipped=integ([Q(1,2),Q(-2),Q(2)],Q(1,2));
const three=add(two,mul(Q(-1),clipped));
const vol3=add(add(Q(27,6),mul(Q(-3),one)),add(mul(Q(3),two),mul(Q(-1),three)));
coeff(one,Q(7,6),"single cut volume");
coeff(two,Q(1,3),"two-cut intersection");
coeff(three,Q(1,4),"three-cut intersection");
coeff(vol2,Q(1,2),"B2 volume");
coeff(vol3,Q(7,4),"B3 volume");
coeff(mul(Q(2,2),vol2),Q(1,2),"pair coefficient");
coeff(mul(Q(2,6),vol3),Q(7,12),"triple coefficient");
console.log("OK: "+checks+" exact geometry/volume checks.");
