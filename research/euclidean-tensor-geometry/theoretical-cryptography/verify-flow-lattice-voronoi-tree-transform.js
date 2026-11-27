'use strict';
const assert=require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;
const Q=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(b<0n)[a,b]=[-a,-b];assert(b>0n);const g=gcd(a,b);return [a/g,b/g];};
const Z=Q(0),I=Q(1),N=([a,b])=>Q(-a,b),A=([a,b],[c,d])=>Q(a*d+b*c,b*d);
const M=([a,b],[c,d])=>Q(a*c,b*d),D=(a,[c,d])=>M(a,Q(d,c));
const S=(a,b)=>A(a,N(b)),sum=x=>x.reduce(A,Z),prod=x=>x.reduce(M,I);
const num=([a,b])=>Number(a)/Number(b);
const ids=n=>Array.from({length:n},(_,i)=>i);
const matrix=(n,m,fn)=>ids(n).map(i=>ids(m).map(j=>fn(i,j)));
const trace=a=>sum(a.map((r,i)=>r[i]));
const dot=(a,b)=>sum(a.map((x,i)=>M(x,b[i])));
const multiply=(a,b)=>matrix(a.length,b[0].length,(i,j)=>dot(a[i],b.map(r=>r[j])));
let exact=0, numerical=0;
const eq=(a,b)=>{assert.deepEqual(a,b);exact++;};
const near=(a,b,relative=5e-11)=>{assert(Math.abs(a-b)<relative*(1+Math.abs(a)+Math.abs(b)),[a,b]);numerical++;};
function invDet(a){
  const n=a.length,T=a.map((r,i)=>r.concat(ids(n).map(j=>i===j?I:Z)));
  let det=I;
  for(let k=0;k<n;k++){
    const l=T.findIndex((r,i)=>i>=k&&r[k][0]);assert(l>=0);
    if(l!==k){[T[l],T[k]]=[T[k],T[l]];det=N(det);}
    const z=T[k][k];det=M(det,z);
    for(let j=k;j<2*n;j++)T[k][j]=D(T[k][j],z);
    for(let i=0;i<n;i++)if(i!==k){
      const z=T[i][k];for(let j=k;j<2*n;j++)T[i][j]=S(T[i][j],M(z,T[k][j]));
    }
  }
  return [T.map(r=>r.slice(n)),det];
}
function info(n,E,T,r){
  const pa=Array(n).fill(-1),ed=Array(n).fill(-1),sg=Array(E.length).fill(0),queue=[r];pa[r]=r;
  for(let q=0;q<queue.length;q++){
    const x=queue[q];
    for(const j of T){
      const [a,b]=E[j],y=a===x?b:b===x?a:-1;
      if(y<0||pa[y]>=0)continue;
      pa[y]=x;ed[y]=j;sg[j]=a===y?1:-1;queue.push(y);
    }
  }
  return queue.length===n?{pa,ed,sg}:null;
}
function trees(n,E){
  const out=[];
  function pick(i,T){
    if(T.length===n-1){if(info(n,E,T,0))out.push(T);return;}
    for(let j=i;j<E.length;j++)pick(j+1,T.concat(j));
  }
  pick(0,[]);return out;
}
function flow(n,E,T,sample){
  const f=E.map(()=>0);
  for(let j=0;j<E.length;j++)if(!T.includes(j)){
    const [a,b]=E[j],i=info(n,E,T,a),k=1+((11*sample+13*j)%5);
    f[j]+=k;let x=b;
    while(x!==a){f[i.ed[x]]+=i.sg[i.ed[x]]*k;x=i.pa[x];}
  }
  const q=ids(n).map(()=>0);for(const [i,[a,b]] of E.entries()){q[a]+=f[i];q[b]-=f[i];}
  eq(q,ids(n).map(()=>0));return f;
}
function cofactor(B,r){return B.filter((_,i)=>i!==r).map(row=>row.filter((_,j)=>j!==r));}
function numericDet(a){
  const T=a.map(r=>r.slice()),n=a.length;let d=1;
  for(let j=0;j<n;j++){
    let k=j;for(let i=j+1;i<n;i++)if(Math.abs(T[i][j])>Math.abs(T[k][j]))k=i;
    if(k!==j){[T[k],T[j]]=[T[j],T[k]];d=-d;}
    d*=T[j][j];
    for(let i=j+1;i<n;i++){const c=T[i][j]/T[j][j];for(let l=j+1;l<n;l++)T[i][l]-=c*T[j][l];}
  }
  return d;
}
const sinc=x=>Math.abs(x)<1e-10?1:Math.sinh(x/2)/(x/2);
function trial(n,E,T,w,sample,closed=null){
  const f=flow(n,E,T[0],sample),v=f.map((x,i)=>x*w[i]),c=w.map(x=>Q(1,x));
  const tau=sum(T.map(p=>prod(p.map(j=>c[j]))));
  const full=matrix(n,n,()=>Z), K=matrix(n,n,()=>Z);
  for(const [i,[a,b]] of E.entries()){
    full[a][a]=A(full[a][a],c[i]);full[b][b]=A(full[b][b],c[i]);
    full[a][b]=S(full[a][b],c[i]);full[b][a]=S(full[b][a],c[i]);
    const k=Q(f[i],2);K[a][b]=A(K[a][b],k);K[b][a]=S(K[b][a],k);
  }
  for(const r of ids(n)){
    const rootInfos=T.map(p=>info(n,E,p,r).sg);
    const [inv,det]=invDet(cofactor(full,r));eq(det,tau);
    const m=ids(n).filter(i=>i!==r);
    const R=E.map(([a,b])=>{const x=m.map(j=>Q((j===a?1:0)-(j===b?1:0)));
      return dot(x,inv.map(row=>dot(row,x)));
    });
    for(const [i,C] of c.entries()){
      const p=D(sum(T.filter(P=>P.includes(i)).map(P=>prod(P.map(j=>c[j])))),tau);
      eq(p,M(C,R[i]));
    }
    let center=Z,expected=Z;
    for(const [j,P] of T.entries()){
      const w=D(prod(P.map(i=>c[i])),tau), k=Q(-P.reduce((s,i)=>s+rootInfos[j][i]*v[i],0),2);
      center=A(center,M(w,k));
      const u=v.reduce((s,x,i)=>s+(P.includes(i)?0:x*x),0);
      expected=A(expected,M(w,A(M(k,k),Q(u,12))));
    }
    eq(center,Z);
    const IK=multiply(inv,cofactor(K,r));
    const first=Q(v.reduce((s,x)=>s+x*x,0),12);
    const second=sum(v.map((a,i)=>M(Q(a*a,6),M(c[i],R[i]))));
    const actual=S(A(first,second),trace(multiply(IK,IK)));
    eq(actual,expected);assert(actual[0]>0n);exact++;
    if(closed)eq(expected,M(closed,Q(v.reduce((s,x)=>s+x*x,0))));
    for(const scale of [.01,.04,.09]){
      const x=v.map(v=>scale*v);
      const L=matrix(n,n,()=>0);
      const bern=z=>z===0?1:z/Math.expm1(z);
      for(const [i,[a,b]] of E.entries()){
        const be=num(c[i])*bern(x[i]),ba=num(c[i])*bern(-x[i]);
        L[a][a]+=be;L[a][b]-=be;L[b][b]+=ba;L[b][a]-=ba;
      }
      for(let j=0;j<n;j++)near(L.reduce((s,row)=>s+row[j],0),0);
      const projected=x.reduce((p,a)=>p*sinc(a),1);
      const fromDet=projected*numericDet(cofactor(L,r))/num(tau);
      const fromTrees=T.reduce((s,P,i)=>{
        const shift=-P.reduce((x,j)=>x+rootInfos[i][j]*v[j],0)*scale/2;
        const cor=x.reduce((p,a,j)=>p*(P.includes(j)?1:sinc(a)),1);
        return s+num(prod(P.map(j=>c[j])))*Math.exp(shift)*cor;
      },0)/num(tau);
      near(fromDet,fromTrees);assert(fromDet>projected);numerical++;
    }
  }
}
const full=n=>ids(n).flatMap(i=>ids(n).filter(j=>j>i).map(j=>[i,j]));
const bi=(m,n)=>ids(m).flatMap(i=>ids(n).map(j=>[i,m+j]));
const sets=[[3,full(3)],[4,full(4)],[5,full(5)],[5,bi(2,3)],[6,bi(3,3)],
  [2,[[0,1],[1,0],[1,0],[0,1]]],[4,[[0,1],[1,2],[2,0],[1,3]]]];
for(const [n,E] of sets){
  const T=trees(n,E);
  for(let s=0;s<7;s++)trial(n,E,T,E.map((_,i)=>1+((11*s+9*i+7*s*i)%13)),s);
}
for(const m of [3,4,5]){
  const E=full(m);trial(m,E,trees(m,E),E.map(()=>1),2,A(A(Q(1,12),Q(1,3*m)),Q(1,2*m*m)));
}
for(const [m,n] of [[2,2],[2,3],[3,3]]){
  const E=bi(m,n);trial(m+n,E,trees(m+n,E),E.map(()=>1),3,A(Q(1,12),Q(m+n+2,6*m*n)));
}
console.log('PASS',exact,'exact tree/covariance checks and',numerical,'directed transform checks');
