'use strict';
// Only small generated finite-field probability spaces; no external inputs.
let checks=0, samples=0;
function check(test,msg){if(!test)throw Error(msg);++checks;}
function num(n,p){return ((n%p)+p)%p;}
function fld(p,modulus,q){
  const d=modulus.length,N=p**d;
  const digits=x=>Array.from({length:d},(_,i)=>Math.floor(x/p**i)%p);
  const ds=Array.from({length:N},(_,x)=>digits(x));
  const val=x=>x.reduce((s,c,i)=>s+num(c,p)*p**i,0);
  const A=ds.map(x=>ds.map(y=>val(x.map((v,i)=>v+y[i]))));
  function pmul(x,y){
    const c=Array(2*d-1).fill(0);
    for(let i=0;i<d;i++)for(let j=0;j<d;j++)c[i+j]+=x[i]*y[j];
    for(let i=2*d-2;i>=d;i--)for(let j=0;j<d;j++)c[i-d+j]-=c[i]*modulus[j];
    return val(c.slice(0,d));
  }
  const M=ds.map(x=>ds.map(y=>pmul(x,y)));
  const add=(x,y)=>A[x][y], mul=(x,y)=>M[x][y];
  const neg=x=>val(ds[x].map(v=>-v));
  const sub=(x,y)=>add(x,neg(y));
  const pow=(x,k)=>{let y=1;while(k){if(k%2)y=mul(x,y);x=mul(x,x);k=Math.floor(k/2);}return y;};
  const inv=x=>pow(x,N-2), conj=x=>pow(x,q);
  check(Array.from({length:N-1},(_,i)=>i+1).every(x=>mul(x,inv(x))===1),'field inverse');
  const all=Array.from({length:N},(_,x)=>x), fixed=all.filter(x=>conj(x)===x);
  check(fixed.length===q,'fixed field size');
  const tracePrime=x=>{let t=0,k=q;while(k>1){t=add(t,x);x=pow(x,p);k/=p;}if(t>=p)throw Error('not prime-field trace');return t;};
  return {p,q,N,all,fixed,add,mul,sub,inv,conj,tracePrime};
}
function transpose(A){return Array.from({length:A[0].length},(_,i)=>A.map(row=>row[i]));}
function adjoint(A,F){return transpose(A).map(row=>row.map(F.conj));}
function matmul(A,B,F){const C=transpose(B);return A.map(row=>C.map(col=>row.reduce((s,x,i)=>F.add(s,F.mul(x,col[i])),0)));}
function padd(A,B,F){return A.map((row,i)=>row.map((a,j)=>F.add(a,B[i][j])));}
function rank(A,F){
  if(!A.length||!A[0].length)return 0;
  let B=A.map(row=>row.slice()),r=0;
  for(let j=0;j<B[0].length&&r<B.length;j++){
    const s=B.findIndex((row,i)=>i>=r&&row[j]);
    if(s<0)continue;
    [B[r],B[s]]=[B[s],B[r]];
    const inv=F.inv(B[r][j]);
    for(let i=r+1;i<B.length;i++)if(B[i][j]){
      const c=F.mul(B[i][j],inv);
      for(let k=j;k<B[0].length;k++)B[i][k]=F.sub(B[i][k],F.mul(c,B[r][k]));
    }
    ++r;
  }
  return r;
}
function aux(a,b,F){
  return a.reduce((u,row,i)=>row.reduce((acc,x,j)=>F.add(acc,F.mul(x,b[j][i])),u),0);
}
function paperG(n,k,t){
  if(k<0||k>n)return 0;
  if(!k||k===n)return 1;
  return paperG(n-1,k,t)+t**(n-k)*paperG(n-1,k-1,t);
}
function hermitian(n,F){
  const H=Array.from({length:n},()=>Array(n).fill(0)),keys=[];
  for(let i=0;i<n;i++)for(let j=i;j<n;j++)keys.push([i,j]);
  const out=[];
  function go(k){
    if(k===keys.length){out.push(H.map(row=>row.slice()));return;}
    const [i,j]=keys[k];
    for(const x of (i===j?F.fixed:F.all)){H[i][j]=x;H[j][i]=F.conj(x);go(k+1);}
  }
  go(0);return out;
}
function unrestricted(n,F){
  const ans=[],a=Array(n*n).fill(0);
  function go(k){
    if(k===a.length){ans.push(Array.from({length:n},(_,i)=>a.slice(i*n,i*n+n)));return;}
    for(const x of F.all){a[k]=x;go(k+1);}
  }
  go(0);return ans;
}
let seed=489197;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
function columns(n,s,F){
  let X;
  do { X=Array.from({length:n},()=>Array.from({length:s},()=>rng(F.N))); } while(rank(X,F)!==s);
  return X;
}
function law(iter,what,F,expect){
  const count=new Map();
  for(const A of iter){
    const t=what(A); count.set(t,(count.get(t)??0)+1);++samples;
  }
  check(count.size===expect,'support cardinality');
  check([...count.values()].every(x=>x*expect===iter.length),'uniform support masses');
}
function intersection(a,b,F){
  return rank(a,F)+rank(b,F)-rank(a.map((row,i)=>row.concat(b[i])),F);
}

const units=[
  [fld(2,[1,1],2),[1,2,3]],
  [fld(3,[1,0],3),[1,2]],
  [fld(2,[1,1,0,0],4),[1,2]],
  [fld(5,[3,0],5),[1,2]]
];
for(const [F,ns] of units)for(const n of ns){
  const set=hermitian(n,F), idx=set.map(A=>rank(A,F));
  check(set.length===F.q**(n*n),'Hermitian seed size');
  // Exact algebraic phase counts for Schmidt's all-rank Fourier identity.
  for(let t=0;t<=n;t++){
    const w=idx.map(k=>paperG(n-k,t,-F.q));
    const j=n-t,c=(-1)**((n+1)*j)*F.q**(n*j);
    for(let h=0;h<set.length;h++){
      const v=Array(F.p).fill(0), A=set[h];
      for(let k=0;k<set.length;k++)if(w[k]){
        v[F.tracePrime(aux(A,set[k],F))]+=w[k];
        ++samples;
      }
      check(v.slice(1).every(x=>x===v[1]),'equal nonzero phase coefficients');
      check(v[0]-v[1]===c*paperG(n-idx[h],j,-F.q),'integer Fourier coefficient');
    }
    check(num(paperG(n,j,-F.q),F.p)===1,'p-unit');
  }

  for(let m=1;m<=n;m++)for(let r=1;r<=n;r++)for(let i=0;i<5;i++){
    const E=columns(n,m,F), W=adjoint(E,F);
    const C=columns(n,r,F);
    const X=i%2?C.map(row=>[...row,row[0]]):C;
    const s=intersection(E,X,F);
    law(set,H=>matmul(matmul(W,H,F),X,F).flat().join(','),F,F.q**(2*m*r-s*s));
  }

  // A biased rank-one correction saturates the single-budget atom bound.
  const reps=Array.from({length:F.N**n-1},(_,i)=>
    Array.from({length:n},(_,j)=>Math.floor((i+1)/F.N**j)%F.N));
  for(const x of reps){
    const pool=Array(F.N).fill(0);
    for(const v of reps){
      const z=x.reduce((s,e,j)=>F.add(s,F.mul(F.conj(e),v[j])),0);
      ++pool[F.mul(F.conj(z),z)]; ++samples;
    }
    const denom=F.q**(2*n-1)*(F.q+1), zero=F.q**(2*n-1)+1;
    pool[0]+=zero;
    check(pool.reduce((a,b)=>a+b,0)===denom,'biased total');
    check(F.fixed.every(z=>pool[z]*F.q===denom),'biased rank-one exact repair');
  }
}

const splitFields=[
  [fld(2,[0],2),3],
  [fld(3,[0],3),2],
  [fld(2,[1,1],4),2]
];
for(const [F,n] of splitFields){
  const seeds=unrestricted(n,F);
  for(let i=0;i<40;i++){
    const [a,b,c,d]=Array.from({length:4},()=>1+rng(n));
    const V1=columns(n,a,F), U1=columns(n,b,F), V2=columns(n,c,F), U2=columns(n,d,F);
    const x=intersection(V1,U2,F), y=intersection(V2,U1,F);
    const W1=transpose(V1),W2=transpose(V2);
    law(seeds,B=>matmul(matmul(W1,B,F),U1,F).flat().join(',')+';'+
      matmul(matmul(W2,transpose(B),F),U2,F).flat().join(','),F,F.N**(a*b+c*d-x*y));
  }
}

// Over GF(4), two correlated individually uniform repair blocks fail the joint requirement.
// Independent diagonal blocks meet it, with exactly 2^(2+2) auxiliary seeds.
const F=units[0][0],Diag=[[0,0],[0,1],[1,0],[1,1]];
const norm=x=>F.mul(x,F.conj(x));
const at=(v,D)=>v.reduce((s,x,i)=>F.add(s,F.mul(D[i],norm(x))),0);
const vec=F.all.flatMap(x=>F.all.map(y=>[x,y])).slice(1);
for(const a of vec)for(const b of vec){
  const by=Array(4).fill(0);
  for(const D1 of Diag)for(const D2 of Diag)++by[at(a,D1)*2+at(b,D2)];
  check(by.every(n=>n===4),'independent product correction');
}
check(new Set(Diag.map(D=>at([1,0],D)*2+at([1,0],D))).size===2,'shared seed does not repair jointly');
console.log('PASS: '+checks+' exact assertions; '+samples+' synthetic evaluations');
