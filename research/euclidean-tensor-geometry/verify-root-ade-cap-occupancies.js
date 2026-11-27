'use strict';
const range=n=>Array.from({length:n},(_,i)=>i),M=n=>Math.max(n-1,2*(n-2),3*Math.min(5,n-3));
function flow(A,B,r){
 const a=A.length,b=B.length,N=a+b+2,s=N-2,t=s+1,f=Array.from({length:N},()=>new Int32Array(N));for(let i=0;i<a;i++)f[s][i]=b;for(let j=0;j<b;j++)f[a+j][t]=a;
 for(let i=0;i<a;i++)for(let j=0;j<b;j++)if(B[j]<r[A[i]])f[i][a+j]=a*b;
 let v=0;for(;;){const pre=Array(N).fill(-1),Q=[s];pre[s]=s;for(let i=0;i<Q.length&&pre[t]<0;i++)for(let j=0;j<N;j++)if(pre[j]<0&&f[Q[i]][j]>0){pre[j]=Q[i];Q.push(j);}if(pre[t]<0)return v;let d=a*b;for(let j=t;j!==s;j=pre[j])d=Math.min(d,f[pre[j]][j]);for(let j=t;j!==s;j=pre[j]){f[pre[j]][j]-=d;f[j][pre[j]]+=d;}v+=d;}
}
let out=[];for(let n=3;n<=10;n++){let total=0,over=0,bad=[];for(let a=1;a<n;a++){const b=n-a;function go(r,last){if(r.length<a){for(let j=0;j<=last;j++)go(r.concat([j]),j);return;}total++;
 if(r.reduce((s,x)=>s+x,0)<=M(n))return;over++;
 let ok=false;for(let na=1;na<=a&&!ok;na++)for(let nb=1;nb<=b&&!ok;nb++)if(na*nb>=2*(na+nb))ok=flow(range(na),range(nb),r)===na*nb;
 if(!ok)bad.push(r);
 }go([],b);}if(bad.length)throw Error('uncovered Ferrers graph');out.push([n,total,over]);}console.log(out);


'use strict';

function dot(a, b) {
  return a.reduce((sum,v,i)=>sum+v*b[i],0n);
}

// Fraction-free determinant with exact row pivoting.
function det(rows) {
  const a=rows.map(row=>row.slice());
  let sign=1n, prev=1n;
  for(let j=0;j<a.length-1;j++){
    const pivot=a.findIndex((row,i)=>i>=j&&row[j]!==0n);
    if(pivot<0)return 0n;
    if(pivot!==j){[a[j],a[pivot]]=[a[pivot],a[j]];sign=-sign;}
    for(let i=j+1;i<a.length;i++)for(let k=j+1;k<a.length;k++){
      const num=a[i][k]*a[j][j]-a[i][j]*a[j][k];
      if(num%prev!==0n)throw Error('division');
      a[i][k]=num/prev;
    }
    for(let i=j+1;i<a.length;i++)a[i][j]=0n;
    prev=a[j][j];
  }
  return sign*a.at(-1).at(-1);
}
function solve(n,expectedRoots,bound,wit) {
  const idx=Array.from({length:n},(_,i)=>i);
  const unit=idx.map(i=>idx.map(j=>BigInt(i===j)));
  const g=idx.map(i=>idx.map(j=>i===j?2n:
    i<n-1&&j<n-1&&Math.abs(i-j)===1 || Math.min(i,j)===2&&Math.max(i,j)===n-1 ? -1n:0n));
  const gdet=det(g);
  const adj=idx.map(i=>idx.map(j=>(i+j)%2===0?
    det(g.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i))):
    -det(g.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
  const roots=unit.map(row=>row.slice()), seen=new Set(roots.map(row=>row.join(',')));
  for(let h=0;h<roots.length;h++)for(const i of idx){
    const r=roots[h].slice();
    r[i]-=dot(g[i],r);
    const key=r.join(',');
    if(!seen.has(key)){seen.add(key);roots.push(r);}
  }
  if(roots.length!==expectedRoots || roots.some(r=>dot(r,g.map(row=>dot(row,r)))!==2n))throw Error('root count');
  const positive=roots.filter(r=>r.every(v=>v>=0n));

 const bit=positive.map((_,i)=>1n<<BigInt(i)),up=positive.map((r,i)=>positive.reduce((m,s,j)=>m|(i!==j&&s.every((x,k)=>x>=r[k])?bit[j]:0n),0n));
 let M=new Set([0n]);for(let k=0;k<bound+1;k++){const next=new Set();for(const m of M)for(let i=0;i<positive.length;i++)if(!(m&bit[i])&&(m&up[i])===up[i])next.add(m|bit[i]);M=next;}
 const gram=(a,b)=>dot(a,g.map(row=>dot(row,b)));let hard=0,count=0,unknown=0,primal=[];const outs=[];
 for(const m of M){count++;const C=positive.filter((r,i)=>m&bit[i]),B=C.filter(r=>!C.some(t=>t!==r&&t.every((x,k)=>x<=r[k])));
 const A=unit.concat(B),rhs=A.map((_,i)=>BigInt(i>=n)),NK=A.length,K=A.map(r=>A.map(s=>gram(r,s))),k=K.map(row=>row.map(Number)),bb=rhs.map(Number);
 let c=A.map(()=>0),v=A.map(()=>0);
 for(let sweep=0;sweep<300;sweep++)for(let i=0;i<NK;i++){const d=Math.max(-c[i],(bb[i]-v[i])/k[i][i]);if(d===0)continue;c[i]+=d;for(let j=0;j<NK;j++)v[j]+=k[j][i]*d;}
 const w=c.map(x=>BigInt(Math.round(x*1000000))),b=dot(w,rhs);if(w.every(x=>x>=0n)&&b>0n&&b*b>=2n*dot(w,K.map(r=>dot(r,w))))continue;
 hard++;const act=idx.slice(0,0);for(let i=0;i<NK;i++)if(Math.abs(v[i]-bb[i])<1e-5)act.push(i);
 const tryAll=act=>{let cert=false;function go(j,J){if(cert)return;if(J.length){const G=J.map(i=>J.map(j=>K[i][j])),D=det(G);if(D>0n){const p=J.map(i=>rhs[i]),z=p.map((_,i)=>det(G.map((row,j)=>row.map((x,k)=>k===i?p[j]:x))));if(z.every(x=>x>=0n)){const nm=dot(z,p);
 if(nm>=2n*D){cert=true;return;}if(K.every((r,i)=>dot(J.map(j=>r[j]),z)>=rhs[i]*D)){const g=idx.map(l=>J.reduce((s,i,j)=>s+z[j]*A[i][l],0n));primal.push([C.length,String(g),String(D),String(nm)]);cert=true;return;}
 }}}if(J.length>=n)return;for(let t=j;t<act.length;t++)go(t+1,J.concat([act[t]]));}go(0,[]);return cert;};
 if(!tryAll(act)&&!tryAll(A.map((_,i)=>i)))unknown++;
 }
 const v=wit.map(BigInt),q=dot(v,adj.map(r=>dot(r,v))),ach=positive.filter(r=>{const z=dot(r,v);return z>0n&&2n*gdet*z*z>q;}).length;
 if(ach!==bound||unknown||primal.length||M.size!==({6:25,7:51,8:24}[n]))throw Error('exceptional certificate');console.log({n,bound,ach,ideals:M.size,exactActiveSetFallbacks:hard});}
solve(6,72,16,[1,0,0,0,0,0]);solve(7,126,27,[0,0,0,0,0,1,0]);solve(8,240,29,[0,0,0,0,0,1,0,0]);