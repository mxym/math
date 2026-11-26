// Exact overlap-polynomial and positivity certificate for the seven-site gap.
const assert=(c,m)=>{if(!c)throw Error(m);};
const range=n=>Array.from({length:n},(_,i)=>i);
const bits=w=>range(6).filter(i=>w>>i&1).length;
const rot=w=>((w<<1)&63)|(w>>5);
function inv(w) {let ones=0,n=0;for (const i of range(6)) {if(w>>i&1)ones++;else n+=ones;}return n;}
const zero=n=>Array(n).fill(0n);
const scale=(a,k)=>a.map(v=>k*v);
function add(a,b){return range(Math.max(a.length,b.length)).map(i=>(a[i]??0n)+(b[i]??0n));}
function mul(a,b){const c=zero(a.length+b.length-1);a.forEach((x,i)=>b.forEach((y,j)=>{c[i+j]+=x*y;}));return c;}
const pow=(a,n)=>range(n).reduce(b=>mul(b,a),[1n]);
function numerator(p,a,b,D) {
 return p.reduce((s,c,i)=>add(s,scale(mul(pow(a,i),pow(b,D-i)),c)),[]);
}
const cos2=[2n,1n,-1n,-2n,-1n,1n];
const words=k=>range(64).filter(w=>bits(w)===k);
for(const r of [1,2,3]){
 let a=zero(9);
 for(const w of words(2)){
  a[inv(w)]+=12n;let s=w;
  for(const j of range(6)){const e=inv(w)+inv(s);assert(e%2===0,"parity");a[e/2]-=5n*cos2[(r*j)%6];s=rot(s);}
 }
 const expected=[
  [2,-8,14,44,76,44,14,-8,2],
  [2,12,34,24,36,24,34,12,2],
  [2,22,14,44,16,44,14,22,2]
 ][r-1].map(BigInt);
 assert(a.every((v,i)=>v===expected[i]),"even polynomial");
}
const Z=zero(19),D=zero(19);
for(const w of words(3)){
 Z[2*inv(w)]++;D[2*inv(w)]+=6n;let s=w;
 for(const j of range(6)){D[inv(w)+inv(s)]--;s=rot(s);}
}
const A=[15n,-26n,15n],B=[5n,-10n,5n];
const p=add(scale(mul(A,D),5n),scale(mul(Z,add(A,[0n,12n])),-6n));
const q=add(mul([0n,2n],mul(A,D)),scale(mul(mul(Z,B),add(add(scale(A,2n),[0n,30n]),scale(B,-5n))),-1n));
const low=numerator(p,[0n,5n],[8n,8n],20), high=numerator(q,[5n,8n],[8n,8n],22);
assert(low.length===21&&low.every(v=>v>0n),"small coupling positivity");
assert(high.length===23&&high.every((v,i)=>i<=20?v>0n:v===0n),"large coupling positivity");
console.log("Seven-site integer overlap/positivity certificate verified.");
