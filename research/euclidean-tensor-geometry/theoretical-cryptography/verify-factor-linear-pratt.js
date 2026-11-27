"use strict";
// Prescribed tiny factor trees only; there is no supplied-input factoring,
// certificate mining, or practical key operation.
const assert=(x,m)=>{if(!x)throw Error(m);};
const forms=new Map([
 [2,[]], [3,[[2,1]]], [5,[[2,2]]], [7,[[2,1],[3,1]]],
 [11,[[2,1],[5,1]]], [13,[[2,2],[3,1]]], [17,[[2,4]]],
 [19,[[2,1],[3,2]]], [257,[[2,8]]], [65537,[[2,16]]],
 [561,[[2,4],[5,1],[7,1]]], // deliberately composite internal label, a Carmichael number
]);
const modexp=(a,k,m)=>{let y=1n;a%=m;while(k){if(k&1n)y=y*a%m;a=a*a%m;k>>=1n;}return y;};
const test=(q,a,ds)=>modexp(a,q-1n,q)===1n&&ds.every(r=>modexp(a,(q-1n)/r,q)!==1n);
const enc=(q,e=0,top=null)=>{
 const ch=top===null?forms.get(q):top;assert(ch!==undefined,"only prescribed structures");
 return "1"+(top===null?"1".repeat(e-1)+"0":"")+ch.map(([r,k])=>enc(r,k)).join("")+"0";
};
const bword=(x,r)=>x.toString(2).padStart(r,"0");
function toyValidate(N,A,B,shape){
 const b=N.toString(2).length,c=Math.ceil(Math.log2(64*(b+1))),T=32*(b+1)**2;
 if(A<0n||B<0n||A>=2n**BigInt(b+c)||B>=2n**BigInt(b+c)||shape.length>7*b+2)return null;
 let i=0,affineChecks=0,excess=0,leaves=0,nodes=0;
 function parse(vt){
  if(shape[i++]!=="1")throw Error("open");
  let e=1;
  if(!vt){while(shape[i]==="1"){i++;e++;}if(shape[i++]!=="0")throw Error("unary");excess+=e-1;nodes++;}
  const children=[];while(shape[i]==="1")children.push(parse(false));
  if(shape[i++]!=="0")throw Error("close");
  let product=1n;const seen=new Set();
  for(const {q,k} of children){
   if(seen.has(q))throw Error("repeated child");seen.add(q);
   for(let j=0;j<k;j++){product*=q;if(product>N)throw Error("cap");}
  }
  if(vt){if(!children.length||product!==N)throw Error("wrong top");return children;}
  if(!children.length){leaves++;return {q:2n,k:e};}
  const q=product+1n;if(q>N)throw Error("node cap");
  const ds=children.map(({q})=>q),large=q>BigInt(T);
  if(large)affineChecks++;
  let hit=false;
  for(let j=0;j<(large?T:Number(q-1n));j++){
   const a=large?(A+BigInt(j)*B)%q:BigInt(j+1);
   if(test(q,a,ds)){hit=true;break;}
  }
  if(!hit)throw Error("Lucas");
  return {q,k:e};
 }
 try{
  const factors=parse(true);
  if(i!==shape.length||nodes>2*b||leaves+excess>b)throw Error("encoding bounds");
  const bytes=bword(A,b+c)+bword(B,b+c)+shape;
  assert(bytes.length<=9*b+2*c+2,"proof bound");
  return {factors,affineChecks};
 }catch{return null;}
}
let examples=0,affineExamples=0;
for(const roots of [
 [[2,1]],[[2,3],[3,2],[17,1]],[[11,2],[13,4],[19,1]],[[257,1],[65537,1]],
 [[3,8],[5,6],[7,3],[65537,2]],
]){
 const N=roots.reduce((x,[q,e])=>x*BigInt(q)**BigInt(e),1n),str=enc(0,0,roots);
 const r=toyValidate(N,3n,1n,str);
 assert(r!==null&&r.factors.length===roots.length&&r.factors.every(({q,k},i)=>q===BigInt(roots[i][0])&&k===roots[i][1]),"toy structure");
 assert(toyValidate(N+1n,3n,1n,str)===null,"wrong top accepted");
 if(r.affineChecks){affineExamples++;assert(toyValidate(N,0n,0n,str)===null,"unsupported root seed accepted");}
 examples++;
}
assert(toyValidate(561n,3n,1n,enc(0,0,[[561,1]]))===null,"Carmichael node accepted");
assert(toyValidate(4n,3n,1n,enc(0,0,[[2,1],[2,1]]))===null,"duplicate top node accepted");
let pairs=0,bias=0,secondMoments=0;
for(const q of [3,5,7,11,13,17,19]){
 const K=Math.min(q,7),Q=BigInt(q),ds=forms.get(q).map(([d])=>BigInt(d));
 const prim=new Set(Array.from({length:q},(_,a)=>a).filter(a=>test(Q,BigInt(a),ds)));
 for(let i=0;i<K;i++)for(let j=i+1;j<K;j++){
  const occupied=new Set();
  for(let a=0;a<q;a++)for(let b=0;b<q;b++)occupied.add(((a+i*b)%q)*q+(a+j*b)%q);
  assert(occupied.size===q*q,"affine pair uniformity");pairs++;
 }
 let failed=0;
 for(let a=0;a<q;a++)for(let b=0;b<q;b++)
  if(!Array.from({length:K},(_,j)=>(a+j*b)%q).some(x=>prim.has(x)))failed++;
 assert(failed*K*prim.size<=q**3,"second moment existence");secondMoments++;
 for(const T of [16,32,64,128,256]){
  const cnt=Array(q).fill(0);for(let a=0;a<T;a++)cnt[a%q]++;
  const tvNumer=cnt.reduce((s,c)=>s+Math.abs(c*q-T),0);
  assert(tvNumer<=2*q*q,"seed bias");bias++;
 }
}
assert(affineExamples>0,"missing large branch");
console.log({examples,affineExamples,pairs,bias,secondMoments,carmichaelAndDuplicateRejected:true});