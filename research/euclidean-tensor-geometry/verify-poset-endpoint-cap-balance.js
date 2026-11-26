'use strict';
// Exact three-chain path counts. Test examples need not satisfy the deliberately
// conservative analytic k/n cutoff in PosetEndpointCapBalance.md.
const assert=(c,s)=>{if(!c)throw Error(s);};
const structure=(n,relations)=>{
  const N=3*n, id=(i,j)=>i*n+j-1, R=Array.from({length:N},()=>Array(N).fill(false));
  for(let i=0;i<3;i++)for(let j=1;j<n;j++)R[id(i,j)][id(i,j+1)]=true;
  for(const [i,a,j,b] of relations)R[id(i,a)][id(j,b)]=true;
  for(let k=0;k<N;k++)for(let i=0;i<N;i++)if(R[i][k])for(let j=0;j<N;j++)if(R[k][j])R[i][j]=true;
  const H=R.map((row,i)=>row.map((v,j)=>v&&!R.some((q,k)=>row[k]&&q[j])));
  assert(!R.some((row,i)=>row[i]),'cycle in directed order');
  const E=(i,j)=>H[i][j]||H[j][i];
  const conn=adj=>{
    const seen=new Set([0]),Q=[0];while(Q.length){const i=Q.pop();for(let j=0;j<N;j++)if(!seen.has(j)&&adj(i,j)){seen.add(j);Q.push(j);}}
    return seen.size===N;
  };
  assert(conn(E)&&conn((i,j)=>i!==j&&!R[i][j]&&!R[j][i]),'decomposition');
  const deg=H.map((row,i)=>row.reduce((s,b,j)=>s+Number(b||H[j][i]),0));
  assert(deg[id(1,2)]===6&&deg.filter(d=>d===6).length===1,'degree six');
  const cycle=[id(0,1),id(0,2),id(1,3),id(1,2)];
  assert(cycle.every((v,i)=>E(v,cycle[(i+1)%4])),'no square');
  const a=id(0,2),b=id(0,3),c=id(1,2),d=id(1,3);
  assert(R[a][b]&&R[c][d]&&R[a][d]&&!R[a][c]&&!R[c][a]&&!R[b][c]&&!R[c][b]&&!R[b][d]&&!R[d][b],'no N');
  const tag=(i,j)=>id(i,j);
  const mid=[0,1,2].map(i=>tag(i,Math.floor(n/2)));
  assert(mid.every(i=>mid.every(j=>!R[i][j])),'not width three');
  assert([0,1].every(i=>[Math.floor(n/2),Math.floor(n/2)+1].every(j=>[Math.floor(n/2),Math.floor(n/2)+1].every(k=>!R[tag(i,j)][tag(1-i,k)]))),'no 2+2');
  // Color refinement certifies that each vertex is fixed by every automorphism.
  let C=Array(N).fill(0);
  for(let t=0;t<N;t++){
    const newId=new Map();
    C=C.map((c,i)=>{
      const left=[],right=[];
      for(let j=0;j<N;j++){if(R[j][i])left.push(C[j]);if(R[i][j])right.push(C[j]);}
      const key=JSON.stringify([c,left.sort(),right.sort()]);
      if(!newId.has(key))newId.set(key,newId.size);
      return newId.get(key);
    });
    if(newId.size===N)return;
  }
  throw Error('refinement did not prove asymmetry');
};
function count(n,k,rels){
  const W=n+1,S=W**3, step=[W*W,W,1], id=(i,j,k)=>i*step[0]+j*step[1]+k;
  const req=Array.from({length:3},()=>Array.from({length:n+1},()=>[]));
  for(const [from,at,to,bt] of rels)req[to][bt].push([from,at]);
  const ok=(q,c)=>q[c]<n&&req[c][q[c]+1].every(([a,b])=>q[a]>=b);
  const F=Array(S).fill(0n),T=Array(S).fill(0n);
  F[0]=1n; T[S-1]=1n;
  for(let i=0;i<=n;i++)for(let j=0;j<=n;j++)for(let l=0;l<=n;l++){
    const z=id(i,j,l),q=[i,j,l];
    if(!F[z])continue;
    for(let c=0;c<3;c++)if(ok(q,c))F[z+step[c]]+=F[z];
  }
  for(let i=n;i>=0;i--)for(let j=n;j>=0;j--)for(let l=n;l>=0;l--){
    const z=id(i,j,l),q=[i,j,l];
    for(let c=0;c<3;c++)if(ok(q,c))T[z]+=T[z+step[c]];
  }
  const ext=F[S-1];
  assert(ext===T[0]&&ext>0n,'path count mismatch');
  const a=k+Math.ceil((n-2*k)/2), J=Array(W).fill(0n);
  for(let j=0;j<=n;j++)for(let l=0;l<=n;l++){
    const z=id(a-1,j,l);
    if(ok([a-1,j,l],0))J[j]+=F[z]*T[z+step[0]];
  }
  assert(J.reduce((a,b)=>a+b,0n)===ext,'transition distribution mismatch');
  let part=0n,best=-1n,bestCount=0n,ix=0;
  for(let j=1;j<=n;j++){
    part+=J[j-1];
    if(j<k||j>n-k+1)continue;
    const err=2n*part-ext, abs=err<0n?-err:err;
    if(best<0n||abs<best){best=abs;bestCount=part;ix=j;}
  }
  assert(3n*bestCount>=ext&&3n*bestCount<=2n*ext,'checked fixture not balanced');
  return [n,a,ix,String(bestCount),String(ext)];
}
function rel(n){
  return [[0,1,1,2],[2,1,1,2],[1,2,0,n-1],[1,2,2,n-2],[0,2,1,3]];
}
const result=[];
for(let n=8;n<=24;n+=1){structure(n,rel(n));result.push(count(n,3,rel(n)));}
for(let bits=0;bits<16;bits++){
  const n=18,k=6,R=rel(n);
  for(let i=3;i<=6;i++)if(bits&(1<<(i-3)))R.push([0,i,2,i]);
  structure(n,R);result.push(count(n,k,R));
}
for(const n of [12,20,32,48]){
  // Heavier conditioning: chain order for early cap and opposite for late cap.
  const k=Math.floor(n/5),R=[[0,k,1,1],[1,k,2,1],[2,n,1,n-k+1],[1,n,0,n-k+1]];
  result.push(count(n,k,R));
}
const out=typeof console==='undefined'?text:console.log;
out('verified '+result.length+' fixtures');
out('n | index in A | index in B | favorable extensions | total extensions');
for(const r of result)out(r.join(' | '));
