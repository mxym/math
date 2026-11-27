'use strict';
/* Fixed affine-shell and exact constant replay for the Leech cold-spot note.
 * No external data, packages, or computation of the Leech lattice needed. */
const assert=require('node:assert/strict');
const r=n=>Array.from({length:n},(_,i)=>i);
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
const add=(a,b,lambda=1)=>a.map((x,i)=>x+lambda*b[i]);
const norm=a=>Math.hypot(...a);
let exact=0,numerical=0;
function ck(x,y){assert.deepEqual(x,y);exact++;}
function check(v){assert(v);exact++;}
function close(v,w,rtol=1e-10){
  assert(Math.abs(v-w)<=rtol*Math.max(1,Math.abs(v),Math.abs(w)),String([v,w]));numerical++;
}
function minorDet(M){
  const A=M.map(a=>a.map(BigInt)),n=A.length;
  if(!n)return 1n;let d=1n,sign=1n;
  for(let i=0;i<n-1;i++){
    let k=i;while(k<n&&!A[k][i])k++;if(k===n)return 0n;
    if(k!==i){[A[i],A[k]]=[A[k],A[i]];sign=-sign;}
    const p=A[i][i];
    for(let l=i+1;l<n;l++){for(let m=i+1;m<n;m++){
      const x=A[l][m]*p-A[l][i]*A[i][m];assert.equal(x%d,0n);A[l][m]=x/d;
    }A[l][i]=0n;}d=p;
  }
  return sign*A[n-1][n-1];
}
function G(m,edges){
  const z=r(m.length).map(i=>r(m.length).map(j=>i===j?2:0));
  for(const [i,j,w=1] of edges){z[i][j]=-w;z[j][i]=-w;}
  ck(z.map(row=>dot(row,m)),r(m.length).map(()=>0));
  ck(minorDet(z),0n);
  const root=z.slice(1).map(a=>a.slice(1));
  for(let i=1;i<=root.length;i++)check(minorDet(root.slice(0,i).map(row=>row.slice(0,i)))>0n);
  return {z,root};
}
const Efinite=[[1,3],[2,4],[3,4],[4,5],[5,6],[6,7],[7,8]];
const E6=G([1,1,2,2,3,2,1],[[0,2],...Efinite.filter(v=>Math.max(...v)<=6)]);
const E7=G([1,2,2,3,4,3,2,1],[[0,1],...Efinite.filter(v=>Math.max(...v)<=7)]);
const marks=[1,2,3,4,6,5,4,3,2];
const E8=G(marks,[[0,8],...Efinite]);
ck(minorDet(E6.root),3n);ck(minorDet(E7.root),2n);ck(minorDet(E8.root),1n);
for(let rank=1;rank<=24;rank++){
  const m=Array(rank+1).fill(1);
  G(m,rank===1?[[0,1,2]]:r(rank+1).map(i=>[i,(i+1)%(rank+1)]));
}
for(let rank=4;rank<=24;rank++){
  const m=r(rank+1).map(i=>i<=1||i>=rank-1?1:2);
  G(m,[[0,2],[1,2],[rank-2,rank-1],[rank-2,rank],...r(rank-4).map(i=>[2+i,3+i])]);
  ck(m.reduce((a,b)=>a+b,0),2*rank-2);
}
function markProduct(m){return m.reduce((a,b)=>a*BigInt(b)**BigInt(b),1n);}
const P8=2n**26n*3n**12n*5n**5n;
ck(markProduct(marks),P8);
const p6=[1,1,1,2,2,2,3],p7=[1,1,2,2,2,3,3,4];
ck(markProduct(p6),2n**6n*3n**3n);ck(markProduct(p7),2n**14n*3n**6n);
for(const [ms,lo,hi] of [[p6,6447n,6448n],[p7,7279n,7280n],[marks,8107n,8108n]]){
  const h=BigInt(ms.reduce((a,b)=>a+b,0)),p=markProduct(ms);
  const target=(1000n*h)**h;
  check(p*lo**h<target);check(target<p*hi**h);
}
check(31*100>38*81); // 2 log(2) - 1 > 31/81 > 0.38.
// Check uniform lower excess across all rank-24 ADE multisets,
// not merely those satisfying the Niemeier Coxeter-number constraints.
const types=[...r(24).map(i=>[i+1,1000,'A']),...r(21).map(i=>[i+4,380,'D']),
  [6,447,'E6'],[7,279,'E7'],[8,107,'E8']];
let partitions=0,winner=0;
function multisets(left,i,excess,e8){
  if(!left){partitions++;if(e8===3){winner++;ck(excess,321);}else check(excess>324);return;}
  for(let j=i;j<types.length;j++){const [rank,q,name]=types[j];if(rank<=left)
    multisets(left-rank,j,excess+q,e8+(name==='E8'?1:0));}
}
multisets(24,0,0,0);ck(winner,1);check(partitions>23);
// Actual eight-dimensional affine E8 shell in the chosen labeling.
const simple=[
  [1,-1,-1,-1,-1,-1,-1,1],[2,2,0,0,0,0,0,0],[-2,2,0,0,0,0,0,0],
  [0,-2,2,0,0,0,0,0],[0,0,-2,2,0,0,0,0],[0,0,0,-2,2,0,0,0],
  [0,0,0,0,-2,2,0,0],[0,0,0,0,0,-2,2,0]
].map(v=>v.map(x=>x/2));
const s0=r(8).map(j=>-simple.reduce((s,a,i)=>s+marks[i+1]*a[j],0));
const S=[s0,...simple];
ck(S.map(x=>S.map(y=>dot(x,y))),E8.z);
function solve(M,b){
  const A=M.map((r,i)=>[...r,b[i]]),n=A.length;
  for(let i=0;i<n;i++){
    let p=i;for(let j=i+1;j<n;j++)if(Math.abs(A[j][i])>Math.abs(A[p][i]))p=j;
    assert(Math.abs(A[p][i])>1e-13);[A[p],A[i]]=[A[i],A[p]];
    const d=A[i][i];A[i]=A[i].map(x=>x/d);
    for(let j=0;j<n;j++)if(j!==i){const q=A[j][i];A[j]=add(A[j],A[i],-q);}
  }
  return A.map(row=>row[n]);
}
const logP=26*Math.log(2)+12*Math.log(3)+5*Math.log(5),gamma=logP/30;
const b=marks.slice(1).map(d=>Math.log(d)-gamma);
const u=solve(simple,b.map(x=>x/2));
function jets(v){
  const w=S.map(s=>Math.exp(2*dot(v,s))),f=w.reduce((a,b)=>a+b,0);
  const g=r(8).map(i=>2*S.reduce((s,x,j)=>s+x[i]*w[j],0));
  const H=r(8).map(i=>r(8).map(k=>4*S.reduce((s,x,j)=>s+x[i]*x[k]*w[j],0)));
  return {f,g,H};
}
const U=jets(u),M=3*U.f,l2=3*dot(u,u);
close(M,90*Math.exp(-gamma));close(M,24.32239537548181);
close(l2,2.6117389956380643);
close(l2,3*dot(b,solve(E8.root,b))/4);
for(let i=0;i<S.length;i++)close(2*dot(u,S[i]),Math.log(marks[i])-gamma);
close(norm(U.g),0);
const slope=solve(U.H,u).map(x=>2*M*x);
let lastPositionError=0,lastValueError=0;
for(const alpha of [1024,2048,4096,8192]){
  let v=u.slice();
  for(let step=0;step<8;step++){
    const {f,g,H}=jets(v);
    const grad=add(g.map(z=>z/f),v,-6/alpha);
    const h=H.map((row,i)=>row.map((x,j)=>x/f-g[i]*g[j]/(f*f)-(i===j?6/alpha:0)));
    v=add(v,solve(h,grad),-1);
  }
  const {f,g}=jets(v);
  close(norm(add(g.map(x=>x/f),v,-6/alpha)),0);
  const err=norm(add(add(v,u,-1),slope,-1/alpha));
  const val=3*f*Math.exp(-3*dot(v,v)/alpha),en=Math.abs(val-M*(1-l2/alpha));
  if(lastPositionError){assert(lastPositionError/err>3.8&&lastPositionError/err<4.25);numerical++;}
  if(lastValueError){assert(lastValueError/en>3.8&&lastValueError/en<4.25);numerical++;}
  lastPositionError=err;lastValueError=en;
}
console.log('PASS: '+exact+' exact checks and '+numerical+' numerical checks; '+partitions+' ADE multisets; E8^3 coefficient '+M);
