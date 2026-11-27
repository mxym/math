"use strict";
// Exact small certificate for the depth-40 witness and the two primitive
// determinant state lists. No graph search, dependencies or network access.
const assert = require("node:assert/strict");
const A=[5,1,1,1,3,1,2,6,2,12,3,1,2,1,1,3,5,11,1,2,1,10,5,1,6,1,4,1,1,2,2,3,2,2,3,2,2,1,1,4,1];
const B=[6,1,5,10,1,2,1,11,5,2,1,2,5,1,1,2,5,2,1,2,3,2,1,2,5,2,1,1,5,2,1,2,5,11,1,2,1,10,5,1,6,1,4,1,1,2,2,3,2,2,3,2,2,1,1,4,1];
// Four reduced entries followed by the packed counter, letter*12+length-1.
const raw=[
  [2,0,1,1,8],
  [3,1,2,2,3],
  [5,3,4,4,0],
  [5,3,3,5,13],
  [5,3,1,7,16],
  [5,3,2,14,22],
  [10,6,7,17,16],
  [20,12,7,17,13],
  [40,24,27,29,0],
  [67,53,54,58,17],
  [134,106,121,111,13],
  [147,101,121,111,0],
  [147,101,95,121,13],
  [147,101,43,141,16],
  [251,61,43,141,0],
  [502,122,43,141,1],
  [545,263,86,282,12],
  [545,263,172,564,13],
  [545,263,344,1128,15],
  [545,263,143,1993,21],
  [1090,526,143,1993,16],
  [2180,1052,143,1993,13],
  [4360,2104,2323,3045,0],
  [6397,1163,2323,3045,2],
  [12794,2326,2323,3045,6],
  [15117,5371,4646,6090,2],
  [15117,5371,9292,12180,0],
  [15117,5371,3467,18989,13],
  [30234,10742,3467,18989,12],
  [57001,2495,3467,18989,1],
  [57001,2495,6934,37978,0],
  [57001,2495,13868,75956,12],
  [114002,4990,70869,78451,3],
  [184871,83441,141738,156902,0],
  [326609,240343,283476,313804,13],
  [326609,240343,240343,387265,17],
  [412875,93421,240343,387265,0],
  [825750,186842,240343,387265,1],
  [1651500,373684,240343,387265,4],
  [1891843,760949,480686,774530,1],
];
const P=[-14733n,-5926n,1891843n,760949n];

let checks=0;
function ok(x,msg) {++checks;assert.ok(x,msg);}
function eq(a,b) {++checks;assert.equal(a,b);}
const I=[1n,0n,0n,1n], L=[1n,1n,0n,1n],R=[1n,0n,1n,1n];
const key=M=>M.join(",");
const det=([a,b,c,d])=>a*d-b*c;
const flip=([a,b,c,d])=>[d,c,b,a];
const adj=([a,b,c,d])=>[d,-b,-c,a];
const mul=([a,b,c,d],[e,f,g,h])=>[a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h];
const Dy=j=>[2n**BigInt(j),0n,0n,1n];
function reduced(M) {
  const [a,b,c,d]=M;
  return a>c&&d>b&&b>=0n&&c>=0n;
}
function primitive(M) { return M.some(x=>x%2n!==0n); }
function division(M,N) {
  const d=det(N), A=mul(M,adj(N)).map(x=>{eq(x%d,0n);return x/d;});
  return A;
}
// Deliberately use unit row subtraction here, independent of the batched
// quotients and fingerprints of the large earlier certificate.
function reduce(M,emit=()=>{}) {
  let [a,b,c,d]=M;
  for (;;) {
    if(a>=c&&b>=d){a-=c;b-=d;emit(0);}
    else if(c>=a&&d>=b){c-=a;d-=b;emit(1);}
    else return [a,b,c,d];
  }
}

function smallList(D) {
  const all=new Set();
  for(let a=1n;a<=D;++a) for(let d=1n;d<=D;++d)
    for(let b=0n;b<d;++b) for(let c=0n;c<a;++c) {
      const M=[a,b,c,d];if(a*d-b*c===D&&primitive(M))all.add(key(M));
    }
  const Q=[[D,0n,0n,1n]], seen=new Set(Q.map(key));
  for(let i=0;i<Q.length;++i) for(const X of [L,R]) {
    const N=reduce(mul(Q[i],X)), t=key(N);
    if(!seen.has(t)){seen.add(t);Q.push(N);}
  }
  eq(seen.size,all.size);
  for(const z of all)ok(seen.has(z));
  return all.size;
}
eq(smallList(2n),4); eq(smallList(4n),12);
eq(raw.length,40);eq(A.length,41);eq(B.length,57);
ok(A[0]!==B[0]);
for(const a of [...A,...B])ok(Number.isInteger(a)&&a>=1&&a<=12);
const mat=raw.map(row=>row.slice(0,4).map(BigInt));
let prev=I;
for(let j=1;j<=40;++j) {
  const M=mat[j-1];
  ok(reduced(M));ok(primitive(M));eq(det(M),2n**BigInt(j));
  eq(det(division(M,prev)),2n);prev=M;
}
eq(det(P),1n);
eq(det(division(mat[39],mul(Dy(40),P))),1n);

let transitions=0;
for(let j=1;j<=40;++j) for(const digits of [A,B]) {
  const M0=mat[j-1], counter0=raw[j-1][4];
  ok(Number.isInteger(counter0)&&counter0>=0&&counter0<24);
  let M=M0, letter=Math.floor(counter0/12), length=counter0%12+1;
  for(const a of digits) {
    const step=mul(M,[1n,BigInt(a),0n,1n]);
    let W=I;
    const N=reduce(step,p=>{
      W=mul(W,p?R:L);
      if(letter===p)++length;
      else {letter=p;length=1;}
      ok(length<=12,"cap crossed");
    });
    ok(reduced(N));
    eq(key(mul(W,N)),key(step));
    // Normalize the other orientation, as the next input letter switches.
    M=flip(N);letter=1-letter;
    ++transitions;
  }
  eq(key(M),key(M0));eq(letter*12+length-1,counter0);
}
eq(transitions,3920);
console.log("Cap-12 supplement checks passed: "+checks+" ("+transitions+" exact returning transitions)");
