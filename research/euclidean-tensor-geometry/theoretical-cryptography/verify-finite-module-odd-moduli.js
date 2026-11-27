"use strict";
// Generated toy checks only. This program is not a short-relation solver.
const assert = (a,b) => { if (a !== b) throw Error(`${a} != ${b}`); };
const mod = (v,m) => (v % m + m) % m;
const p = 5, Q = p*p, y = 7;
assert(mod(y*y+1,Q),0);
const v = x => { x = mod(x,Q); return x ? (x % p ? 0 : 1) : 2; };
function count(A) {
  const n=A[0].length, x=Array(n).fill(0);
  let found=0;
  for(let code=0;code<Q**n;++code) {
    let m=code;
    for(let j=0;j<n;++j){x[j]=m%Q;m=Math.floor(m/Q);}
    if(A.every(row => !mod(row.reduce((a,c,j)=>a+c*x[j],0),Q))) ++found;
  }
  return found;
}
let individual=0, normCases=0;
for(let a=-15;a<=15;++a) for(let b=-15;b<=15;++b) {
  if (!(a||b)) continue;
  const z0=a+b*y,z1=a-b*y;
  assert(count([[z0]])*count([[z1]]),p**(v(z0)+v(z1)));
  ++individual;
  assert((a*a+b*b) % p**(v(z0)+v(z1)),0); // determinant (quadratic norm)
  ++normCases;
}
let allPairs=0;
for(let a=0;a<Q;++a) for(let b=0;b<Q;++b){
  const z0=a+b*y,z1=a-b*y;
  const z2=1+a*y,z3=1-a*y;
  assert(count([[z0,z2]])*count([[z1,z3]]),Q**2*p**(Math.min(v(z0),v(z2))+Math.min(v(z1),v(z3))));
  ++allPairs;
}
const abc=[1,-1,y,-y], shell=[];
for(const a of abc) for(const b of abc) shell.push([1,a,b]);
const reflect = x => (Math.abs(x)===y ? -x : x);
const det = ([[a,b,c],[d,e,f],[g,h,i]]) => a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g);
const types = new Map();
for(let i=0;i<shell.length;++i) for(let j=i+1;j<shell.length;++j){
  const A=[shell[i],shell[j]];
  assert(count(A)*count(A.map(row=>row.map(reflect))), Q**2);
  for(let k=j+1;k<shell.length;++k){
    const A=[shell[i],shell[j],shell[k]], A1=A.map(row=>row.map(reflect));
    const vv=[v(det(A)),v(det(A1))].sort().join(",");
    if(!types.has(vv)) {
      // Every pair has a unit 2-minor by residual distinctness; a 3x3
      // matrix then has Smith invariants 1,1,det up to units.
      assert(count(A)*count(A1),p**(v(det(A))+v(det(A1))));
      types.set(vv,A);
    }
  }
}
assert([...types.keys()].sort().join(';'),'0,0;0,1;2,2');
console.log({individual,normCases,twoRowCoefficientTests:allPairs, shellPairs:120, tripleValuationPatterns:[...types.keys()].sort()});

// Mixed split/inert CRT at Q=15: Y^2+1 is irreducible mod 3
// and has two distinct roots ±2 mod 5. Count full-ring outputs directly.
function mul15([a,b],[c,d]) {return [mod(a*c-b*d,15),mod(a*d+b*c,15)];}
let mixed=0;
for(let a=-7;a<=7;++a)for(let b=-7;b<=7;++b) {
  const expect=(a%3===0 && b%3===0 ? 9 : 1)
    *(mod(a+2*b,5)===0 ?5:1)*(mod(a-2*b,5)===0 ?5:1);
  let found=0;
  for(let c=0;c<15;++c)for(let d=0;d<15;++d) if(mul15([a,b],[c,d]).every(x=>x===0)) ++found;
  assert(found,expect);
  assert((a*a+b*b)%expect,0);
  ++mixed;
}
console.log({mixedSplitInertMultiplicationAndNormTests:mixed});

// Common h=1 at Q=3*17,d=8. The local factors at 3 have
// degree 4 (not <=2), whereas at 17 they all have degree 1.
const F=[2,0,1,0,1], H=[2,0,2,0,1];
const pv=F.reduce((a,x,i)=>{H.forEach((y,j)=>a[i+j]+=x*y);return a;},Array(9).fill(0));
assert(pv.map(x=>mod(x,3)).join(),"1,0,0,0,0,0,0,0,1");
const pow=(a,k,m)=>{let b=1;while(k--)b=mod(a*b,m);return b;};
const roots17=Array.from({length:17},(_,i)=>i).filter(i=>pow(i,8,17)===16);
assert(roots17.length,8);
const lift=(a,n=8)=>a.concat(Array(n-a.length).fill(0));
function mul8(a,b){const out=Array(8).fill(0);a.forEach((x,i)=>b.forEach((y,j)=>out[(i+j)%8]+=(i+j<8?1:-1)*x*y));return out;}
function isDiv(a,g,p){
  a=a.map(x=>mod(x,p));
  for(let i=a.length-1;i>=g.length-1;--i){
    const c=a[i]; for(let j=0;j<g.length;++j)a[i-g.length+1+j]=mod(a[i-g.length+1+j]-c*g[j],p);
  }
  return a.every(x=>!x);
}
function kernel3(a){
  let found=0;
  for(let code=0;code<3**8;++code){
    let k=code;const b=[];for(let j=0;j<8;++j){b.push(k%3);k=Math.floor(k/3);}
    if(mul8(a,b).every(x=>x%3===0))++found;
  }
  return found;
}
function detInteger(A){
  if(A.length===0)return 1n;
  return A[0].reduce((t,x,i)=>x===0n?t:t+(i%2?-x:x)*detInteger(A.slice(1).map(row=>row.filter((_,j)=>j!==i))),0n);
}
const threeSeventeen=[
  [1],[3],[17],[51],F,H,[0,2,0,1,0,1], [14,1],[17*2,17,17*1,0,17*1],
  [2,0,1,0,1,17,-17,6],
].map(a=>lift(a));
for(const a of threeSeventeen){
  const deg3=4*Number(isDiv(a,F,3))+4*Number(isDiv(a,H,3));
  const deg17=roots17.filter(r=>mod(a.reduce((n,c,i)=>n+c*pow(r,i,17),0),17)===0).length;
  assert(kernel3(a),3**deg3);
  const A=Array.from({length:8},(_,i)=>mul8(a,lift(Array.from({length:i+1},(_,j)=>Number(i===j)))).map(BigInt));
  assert(detInteger(A)%(3n**BigInt(deg3)*17n**BigInt(deg17)),0n);
}
console.log({commonBlockMixedResidueDegrees:[4,1],cases:threeSeventeen.length});
