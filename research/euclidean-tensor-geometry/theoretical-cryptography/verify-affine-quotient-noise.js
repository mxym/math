'use strict';
// Exact tests for abstract quotient maps on deliberately tiny negacyclic rings.
let checks=0;const ok=x=>{checks++;if(!x)throw Error('check failed');};
const mod=(a,q)=>(a%q+q)%q;
const eq=(a,b)=>a.length===b.length&&a.every((v,i)=>v===b[i]);
function mul(a,b) {
 const d=a.length,c=Array(d).fill(0);
 a.forEach((x,i)=>b.forEach((y,j)=>c[(i+j)%d]+=(i+j<d?1:-1)*x*y));
 return c;
}
const vecs=(q,d)=>Array.from({length:q**d},(_,k)=>Array.from({length:d},(_,i)=>Math.floor(k/q**i)%q));
const times=(A,x)=>A.map(r=>r.reduce((s,v,i)=>s+v*x[i],0));
function matrix(c){const e=vecs(2,c.length).filter(x=>x.reduce((s,y)=>s+y,0)===1);const cols=e.map(x=>mul(c,x));return cols.map((_,i)=>cols.map(col=>col[i]));}
const gram=A=>A.map(r=>A.map(s=>r.reduce((t,x,i)=>t+x*s[i],0)));
const diag=(d,x)=>Array.from({length:d},(_,i)=>Array.from({length:d},(_,j)=>i===j?x:0));
for(const p of [2,3,5]){
 const q=2*p;
 for(const c of [[1,0],[1,1]]){
  const C=matrix(c),A=C.map((r,i)=>r.map((v,j)=>v+p*(i===j?1:-1)));
  for(const a of vecs(q,2))for(const s of vecs(q,2)){
   const src=times(A,mul(a,s)).map(x=>mod(x,p));
   const dst=mul(mul(a,s),c).map(x=>mod(x,p));
   ok(eq(src,dst));
  }
 }
 for(const z of vecs(3,4)){
  const A=[[1+p*(z[0]-1),p*(z[1]-1)],[p*(z[2]-1),1+p*(z[3]-1)]];
  ok(gram(A).every((r,i)=>r[i]>=1));
  if(p>2 && gram(A).every((r,i)=>r[i]===1))ok(A.every((r,i)=>eq(r,diag(2,1)[i])));
 }
 const U=[[1,p],[0,1]],B=gram(U);
 ok((B[0][0]-1)*(B[1][1]-1)-B[0][1]**2===-p*p);
}
ok(gram(matrix([1,0,1,0])).every((r,i)=>eq(r,diag(4,2)[i])));
ok(gram(matrix([1,1,0,0])).some((r,i)=>r.some((x,j)=>i!==j&&x!==0)));
console.log({exactAlgebraChecks:checks});
