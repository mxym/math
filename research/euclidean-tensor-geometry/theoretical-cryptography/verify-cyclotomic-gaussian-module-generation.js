'use strict';
const assert=require('node:assert/strict');
let checks=0;
function check(x,m){assert(x,m);checks++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const mod=(a,p)=>(a%p+p)%p;
let state=0x923069ab;
function pick(p){state=(Math.imul(state,1664525)+1013904223)>>>0;return state%p;}
function rank(A,p) {
 if(!A.length)return 0;
 const B=A.map(r=>r.map(x=>mod(x,p)));let r=0;
 for(let j=0;j<B[0].length&&r<B.length;j++){
  const k=B.findIndex((x,i)=>i>=r&&x[j]!==0);
  if(k<0)continue;
  [B[k],B[r]]=[B[r],B[k]];
  for(let i=r+1;i<B.length;i++)if(B[i][j]!==0){
   const u=B[i][j],v=B[r][j];
   for(let h=j;h<B[0].length;h++)B[i][h]=mod(v*B[i][h]-u*B[r][h],p);
  }
  r++;
 }
 return r;
}
for(const [p,r,m] of [[2,1,2],[2,2,3],[2,2,5],[2,3,4],[2,3,5],[2,3,6],[3,1,4],[3,2,3],[3,2,4],[5,2,3]]) {
 let count=0n;
 const limit=p**(r*m);
 for(let k=0;k<limit;k++){
  const mat=seq(r).map(i=>seq(m).map(j=>Math.floor(k/p**(m*i+j))%p));
  if(rank(mat,p)===r)count++;
 }
 const target=seq(r).reduce((a,i)=>a*(BigInt(p)**BigInt(m)-BigInt(p)**BigInt(i)),1n);
 check(count===target);
}
for(const p of [2,3,5,7,11,17])for(let j=1;j<=8;j++)for(let trial=0;trial<100;trial++){
 // Build a rank-(j-1) top block and a deliberately dependent last row.
 // The repair statement is invariant under each generated row/column operation.
 const top=seq(j-1).map(i=>seq(j).map(k=>Number(i===k)));
 for(let t=0;t<6*j;t++){
  const a=pick(j),b=pick(j),v=pick(p);
  if(a===b)continue;
  for(const row of top)row[b]=mod(row[b]+v*row[a],p);
 }
 check(rank(top,p)===j-1);
 const coef=seq(j-1).map(()=>pick(p));
 const bottom=seq(j).map(k=>mod(top.reduce((a,row,i)=>a+coef[i]*row[k],0),p));
 const old=[...top,bottom];
 check(rank(old,p)===j-1);
 const fresh=seq(j-1).map(()=>pick(p));
 const shouldFail=mod(coef.reduce((a,v,i)=>a+v*fresh[i],0),p);
 let bad=0;
 for(let z=0;z<p;z++){
  const M=old.map((row,i)=>[...row,i===j-1?z:fresh[i]]);
  const failed=rank(M,p)!==j;
  check(failed===(z===shouldFail));
  bad+=Number(failed);
 }
 check(bad===1);
}
function isPrime(x){
 if(x<2)return false;
 for(let i=2;i*i<=x;i++)if(x%i===0)return false;
 return true;
}
const small=seq(300).filter(isPrime);
for(const ram of [2,3,5,7,11])for(let a=1;a<=4;a++){
 const f=ram**a,n=f-f/ram,Q=new Map();
 for(const p of small)if(p!==ram){
  let d=1,z=p%f;
  while(z!==1){z=z*p%f;d++;}
  const norm=BigInt(p)**BigInt(d),fB=BigInt(f);
  check((norm-1n)%fB===0n&&norm>=fB+1n);
  check(n%d===0&&n/d<=n);
  check(!Q.has(norm));Q.set(norm,n/d);
 }
 const H=2*f*small.length;
 for(let u=1;u<=4;u++){
  // A finite truncation of the progression majorizes the actual
  // norm sum term by term, in exact common-denominator arithmetic.
  const R=[...Q.entries()].filter(([x])=>x<=H);
  if(!R.length)continue;
  const maxIdx=Math.max(...R.map(([x])=>Number((x-1n)/BigInt(f))));
  const denom=seq(maxIdx).reduce((z,i)=>z*BigInt(1+f*(i+1))**BigInt(u+1),1n);
  const actual=R.reduce((z,[x,a])=>z+BigInt(a)*(denom/x**BigInt(u+1)),0n);
  const major=seq(maxIdx).reduce((z,i)=>z+BigInt(n)*(denom/BigInt(1+f*(i+1))**BigInt(u+1)),0n);
  check(actual<=major);
 }
}
console.log('PASS: '+checks+' exact checks');
