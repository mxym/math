'use strict';
const assert=require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;
const F=(a,b=1)=>{a=BigInt(a);b=BigInt(b);if(b<0n)[a,b]=[-a,-b];assert(b>0n);
  const g=gcd(a,b);return [a/g,b/g];};
const z=F(0),one=F(1);
const add=([a,b],[c,d])=>F(a*d+b*c,b*d);
const mul=([a,b],[c,d])=>F(a*c,b*d);
const neg=([a,b])=>F(-a,b), sq=a=>mul(a,a);
const sub=(a,b)=>add(a,neg(b)), inv=([a,b])=>F(b,a), div=(a,b)=>mul(a,inv(b));
const sum=a=>a.reduce(add,z),prod=a=>a.reduce(mul,one);
const cmp=([a,b],[c,d])=>a*d-b*c;
let count=0;
const eq=(a,b)=>{assert.deepEqual(a,b);count++;};
const idx=n=>Array.from({length:n},(_,i)=>i);
function determinant(M){
  const A=M.map(r=>r.slice()),n=A.length;let d=one;
  for(let i=0;i<n;i++){
    const j=A.findIndex((r,j)=>j>=i&&r[i][0]);
    if(j<0)return z;
    if(j!==i){[A[i],A[j]]=[A[j],A[i]];d=neg(d);}
    const p=A[i][i];d=mul(d,p);
    for(let r=i+1;r<n;r++){
      const g=div(A[r][i],p);for(let c=i;c<n;c++)A[r][c]=sub(A[r][c],mul(g,A[i][c]));
    }
  }
  return d;
}
const Phi=a=>sum(a.map((x,i)=>mul(sq(x),prod(a.filter((_,j)=>j!==i).map(w=>add(one,mul(F(2),w)))))));
function check(W){
  const m=W.length,d=m-1,I=idx(m),J=idx(d);
  const invs=W.map(inv), H=sum(invs), a=invs.map(x=>div(x,H)),D=mul(H,prod(W));
  eq(sum(a),one);
  const G=J.map(i=>J.map(j=>add(i===j?W[i]:z,W[d])));
  eq(determinant(G),D);
  const g=I.map(j=>J.map(i=>sub(i===j?one:z,a[i])));
  const mean=J.map(i=>sum(I.map(j=>mul(a[j],g[j][i]))));
  eq(mean,J.map(()=>z));
  const C=J.map(i=>J.map(j=>{
    // Integrate independent intervals on each lower facet separately.
    return sum(I.map(k=>mul(a[k],sum(I.map(l=>mul(F(1,l===k?4:12),mul(g[l][i],g[l][j])))))));
  }));
  for(const i of J)for(const j of J)
    eq(C[i][j],div(sum(I.map(k=>mul(add(one,mul(F(2),a[k])),mul(g[k][i],g[k][j])))),F(12)));
  const trace=sum(J.flatMap(i=>J.map(j=>mul(G[i][j],C[i][j]))));
  eq(trace,div(add(sum(W),div(F(m-2),H)),F(12)));
  eq(mul(F(12n**BigInt(d)),determinant(C)),Phi(a));
  let best=z;
  for(let mask=0;mask<2**m;mask++){
    const signs=I.map(i=>(mask>>i)&1?one:F(-1));
    const s=sum(signs);
    const y=J.map(i=>div(sub(signs[i],mul(a[i],s)),F(2)));
    const actual=sum(J.flatMap(i=>J.map(j=>mul(G[i][j],mul(y[i],y[j])))));
    eq(actual,div(sub(sum(W),div(sq(s),H)),F(4)));
    if(cmp(actual,best)>0n)best=actual;
  }
  eq(best,div(sub(sum(W),m%2?inv(H):z),F(4)));
  const U=I.map(()=>F(1,m));
  const base=div(F(BigInt(m+2)**BigInt(m-1)),F(BigInt(m)**BigInt(m)));
  eq(Phi(U),base);
  for(let j=0;j<m;j++)for(let k=j+1;k<m;k++){
    if(cmp(a[j],a[k])!==0n){
      const b=a.slice(), v=div(add(a[j],a[k]),F(2));b[j]=v;b[k]=v;
      assert(cmp(Phi(a),Phi(b))>0n);count++;
    }
  }
  if(a.some(x=>cmp(a[0],x)!==0n)){assert(cmp(Phi(a),base)>0n);count++;}
}
for(let m=3;m<=8;m++){
  check(idx(m).map(()=>one));
  for(let t=0;t<40;t++)check(idx(m).map(i=>F(1+((113*t+71*i+7*t*i)%83),1+((17*t+59*i+i*i)%43))));
}
console.log('PASS',count,'exact determinant, covariance, radius and transfer checks');
