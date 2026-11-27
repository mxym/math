'use strict';
/* Tiny synthetic binary spaces and exact formal polynomial tests. */
const assert=require('node:assert/strict');
let exact=0,numerical=0;
function ck(a,b){assert.deepEqual(a,b);exact++;}
function tr(v){assert(v);exact++;}
function near(a,b){assert(Math.abs(a-b)<3e-10,String([a,b]));numerical++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
function wt(x){let n=0;while(x){x&=x-1;n++;}return n;}
function dot(x,y){return wt(x&y)%2;}
function apply(C,x){return C.reduce((p,v,i)=>x>>i&1?p^v:p,0);}
function space(C){return seq(1<<C.length).map(x=>apply(C,x));}
function orth(A){
  return A.every((a,j)=>A.every((b,i)=>dot(a,b)===Number(i===j)));
}
function diff(A){return A.map((x,i)=>x^(1<<i));}
function rank(C){return Math.log2(new Set(space(C)).size);}
function sigma(A,p){
  const B=diff(A),W=new Map();
  for(let x=0;x<1<<A.length;x++){
    const w=apply(B,x);if(!W.has(w))W.set(w,x);
  }
  const V=[...W.keys()],r=Math.log2(V.length),s=1-p;
  let R=0;
  for(const v of V)for(const w of V)if(!(v&w)){
    ck(dot(v,W.get(w)),dot(w,W.get(v)));
    R+=(dot(v,W.get(w))?-1:1)*p**(wt(v)/2)*s**(wt(w)/2);
  }
  return R/2**r;
}
function direct(A,p){
  const c=Math.sqrt((1+Math.sqrt(p))/2),s=Math.sqrt((1-Math.sqrt(p))/2),n=A.length;
  let tot=0;
  for(let x=0;x<1<<n;x++){const w=wt(x)+wt(apply(A,x));tot+=c**(2*n-w)*s**w;}
  return tot;
}
let checked=0;
function test(A){
  assert(orth(A));const B=diff(A);
  ck(rank(B)<=3,true);checked++;
  const M=sigma(A,.5);near(M,direct(A,.5));
  for(const p of [.125,.3125,.75,.875]){
    const v=sigma(A,p);near(v,direct(A,p));
    assert(v>=M-2e-12);numerical++;
    if(A.some(a=>wt(a)!==1)){assert(v>M+1e-16);numerical++;}
  }
}
for(let n=1;n<=5;n++){
  const odd=seq(1<<n).filter(x=>wt(x)%2);
  function rec(A){
    if(A.length===n){if(rank(diff(A))<=3)test(A);return;}
    for(const a of odd)if(A.every(b=>!dot(a,b)))rec([...A,a]);
  }
  rec([]);
}
// Realize rank-three deviations from four-cell patterns. A rank-three
// basis U and invertible T with T+T^T=U^T U give I+U T^-1 U^T orthogonal.
function fixtures(ns){
  const n=ns.reduce((a,b)=>a+b,0);let a=0,b=0,c=0,j=0;
  for(let pat=0;pat<4;pat++)for(let i=0;i<ns[pat];i++,j++){
    a|=1<<j;if(pat&1)b|=1<<j;if(pat&2)c|=1<<j;
  }
  const U=[a,b,c], signs=new Set();assert(rank(U)===3);
  const Ft=seq(3).map(i=>seq(3).map(j=>dot(U[i],U[j])));
  for(let word=0;word<512;word++){
    const T=seq(3).map(j=>word>>(3*j)&7),Q=space(T);
    if(new Set(Q).size!==8)continue;
    if(seq(3).some(i=>seq(3).some(j=>((T[i]>>j^T[j]>>i)&1)!==Ft[i][j])))continue;
    const A=seq(n).map(i=>(1<<i)^apply(U,Q.indexOf(U.reduce((x,v,j)=>x|((v>>i&1)<<j),0))));
    const e=[1,2,3].map(z=>dot(z<<1,apply(T,1^(z<<1))));
    signs.add(e.reduce((a,b)=>a+b,0));
    test(A);if(signs.size===2)break;
  }
  ck([...signs].sort(),ns[0]%2?[1,3]:[0,2]);
}
for(const ns of [[1,1,1,1],[1,1,1,5],[3,1,3,1],[2,2,2,2],[0,2,2,2]])fixtures(ns);
// Large-rank family is replayed from known simplex weights without
// enumerating any ambient high-dimensional code.
for(let r=1;r<=8;r++){
  const W=seq(1<<r).map(x=>seq((1<<r)-1).map(i=>dot(x,i+1)));
  for(let i=1;i<W.length;i++){
    ck(W[i].reduce((a,b)=>a+b,0),2**(r-1));
    for(let j=1;j<i;j++)tr(W[i].some((x,k)=>x&&W[j][k]));
  }
}
function choose(n,k){
  if(k<0||k>n)return 0;let c=1;for(let j=1;j<=k;j++)c=c*(n-j+1)/j;return c;
}
const h=seq(13).map(i=>choose(12,i)-12*
  (choose(8,i-1)-2*choose(8,i-2)+choose(8,i-3))+97*
  (choose(4,i-2)-4*choose(4,i-3)+6*choose(4,i-4)-4*choose(4,i-5)+choose(4,i-6)));
ck(h,[1,0,91,64,11,960,1842,960,11,64,91,0,1]);
const p=[...seq(25)].map(i=>i%2?0:h[i/2]);
for(let m=0;m<=24;m++){
  let q=0;
  for(let n=0;n<=24;n++)for(let j=0;j<=m;j++)
    q+=p[n]*(-1)**j*choose(n,j)*choose(24-n,m-j);
  ck(q,4096*p[m]);
}
const shadow=seq(6).map(i=>4096*Number(i*4===12)+768*
  (Number(i*4===8)-2*Number(i*4===12)+Number(i*4===16))+97*(-1)**(i-1)*choose(4,i-1));
ck(shadow.slice(1),[97,380,3142,380,97]);
ck(-12*16+2*97,2);tr(48+16*91>1104);
console.log('PASS: '+exact+' exact; '+numerical+' numerical; '+checked+' tested low-rank orthogonal matrices');
