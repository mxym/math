'use strict';
const check=(x,m)=>{if(!x)throw Error(m);};
const pc=x=>{let y=0;while(x){x&=x-1;y++;}return y;};
function matching(n,S){
 let best=0;
 for(let M=0;M<(1<<n);M++){
  const count=pc(M);if(count<=best)continue;
  let used=0,ok=true;
  for(let i=0;i<n;i++)if(M>>i&1){
   const j=(i+1)%n, b=(1<<i)|(1<<j);
   if((used&b)||((S>>i&1)===(S>>j&1))){ok=false;break;}
   used|=b;
  }
  if(ok)best=count;
 }
 return best;
}
function mincut(n,S){
 let best=n;
 for(let V=0;V<(1<<n);V++){
  let cost=pc(S^V);
  for(let i=0;i<n;i++)if((V>>i&1)!==(V>>((i+1)%n)&1))cost++;
  best=Math.min(best,cost);
 }
 return best;
}
function rank(M,p){
 let r=0,n=M.length,m=M[0].length;
 for(let j=0;j<m;j++){
  let i=r;while(i<n&&!M[i][j])i++;if(i===n)continue;
  [M[i],M[r]]=[M[r],M[i]];let e=1;while((e*M[r][j])%p!==1) e++;
  for(let i=r+1;i<n;i++)if(M[i][j]){
   const u=M[i][j]*e%p;
   for(let k=j;k<m;k++)M[i][k]=(M[i][k]-u*M[r][k]+p*p)%p;
  }
  r++;
 }
 return r;
}
function words(q,n){
 return Array.from({length:q**n},(_,j)=>Array.from({length:n},()=>{const a=j%q;j=(j-a)/q;return a;}));
}
function flatten(q,n,S,edge,p){
 const U=[],V=[];for(let j=0;j<n;j++)((S>>j&1)?U:V).push(j);
 const w=new Int32Array(n);
 return words(q,U.length).map(u=>words(q,V.length).map(v=>{
  U.forEach((j,i)=>w[j]=u[i]);V.forEach((j,i)=>w[j]=v[i]);
  let t=1;for(let j=0;j<n;j++)t=t*edge(w[j],w[(j+1)%n])%p;return t;
 }));
}
function alt(n,S){return n%2===0&&Array.from({length:n},(_,i)=>(S>>i&1)!==(S>>((i+1)%n)&1)).every(Boolean);}
// Independent direct q×q trace of E_00 and E_0a+E_a0. Each matrix is a partial permutation.
function hubTrace(w,q,p){
 let z=0;
 for(let start=0;start<q;start++){
  let state=start;
  for(const a of w){
   if(a===0){if(state!==0){state=-1;break;}}
   else if(state===0)state=a;
   else if(state===a)state=0;
   else{state=-1;break;}
  }
  if(state===start)z++;
 }
 return z%p;
}
function hubFlat(q,n,S,p){
 const U=[],V=[];for(let j=0;j<n;j++)((S>>j&1)?U:V).push(j);
 const w=new Int32Array(n),rows=words(q,U.length),cols=words(q,V.length);
 return rows.map(u=>cols.map(v=>{
  U.forEach((j,i)=>w[j]=u[i]);V.forEach((j,i)=>w[j]=v[i]);
  return hubTrace(w,q,p);
 }));
}
let minChecks=0,weightChecks=0,hubChecks=0;
for(let n=3;n<=10;n++)for(let S=0;S<(1<<n);S++){
 const nu=matching(n,S);check(nu===mincut(n,S),'flow '+[n,S]);minChecks++;
 for(const [q,p,maxN] of [[2,3,8],[3,3,7],[4,3,6],[5,5,5],[3,7,6]])if(n<=maxN&&!alt(n,S)){
  const K=(a,b)=>a===b&&a!==0?2:1;
  check(rank(flatten(q,n,S,K,p),p)===q**nu,'weighted rank '+[q,p,n,S]);weightChecks++;
 }
 if(!alt(n,S))for(const [q,p,maxN] of [[2,2,9],[3,2,7],[4,2,6],[5,2,6],[2,3,7],[3,5,6]])if(n<=maxN){
  check(rank(hubFlat(q,n,S,p),p)===q**nu,'colored hub rank '+[q,p,n,S]);hubChecks++;
 }
}
console.log({minChecks,weightChecks,hubChecks});
