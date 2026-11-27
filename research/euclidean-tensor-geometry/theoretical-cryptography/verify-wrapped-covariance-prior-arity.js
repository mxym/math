"use strict";
// Exact identities on generated arrays. No numerical inverse identification.
let tests=0;
function ck(x,m){if(!x)throw new Error(m); ++tests;}
const mat=(r,s,f)=>Array.from({length:r},(_,i)=>Array.from({length:s},(_,j)=>f(i,j)));
const trans=A=>mat(A[0].length,A.length,(i,j)=>A[j][i]);
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0n);
const prod=(A,B)=>{const C=trans(B);return mat(A.length,B[0].length,(i,j)=>dot(A[i],C[j]));};
const gram=A=>prod(A,trans(A));
const plus=(A,B)=>mat(A.length,A[0].length,(i,j)=>A[i][j]+B[i][j]);
const sc=(A,s)=>mat(A.length,A[0].length,(i,j)=>A[i][j]*s);
const rankone=v=>mat(v.length,v.length,(i,j)=>v[i]*v[j]);
const eq=(A,B)=>A.every((r,i)=>r.every((x,j)=>x===B[i][j]));
const cyc=(i,j,w)=>BigInt((13*i+17*j+61*w+7*i*j+11*w*i)%29-14);
for(let n=2;n<=13;n++)for(let w=0;w<21;w++){
  const m=n-(n&1), V=mat(n,m,(i,j)=>cyc(i,j,w)), G=gram(V);
  const anchor=rankone(Array.from({length:n},(_,j)=>cyc(0,j,w)));
  for(let k=-5;k<=5;k++)for(let ell=-4;ell<=4;ell++){
    const a=BigInt(k), b=BigInt(ell), t=a*a+b*b;
    const R=mat(m,m,(i,j)=>i===j?a:(i>>1)===(j>>1)?(i%2?b:-b):0n);
    const Y=prod(V,R);
    ck(eq(gram(Y),sc(G,t)),"two-column Gram dilation");
    if(n&1)ck(eq(plus(gram(Y),anchor),plus(sc(G,t),anchor)),
               "anchored odd-rank dilation");
  }
}
for(let n=3;n<=17;n+=2)for(let k=1;k<=81;k++){
  const w=Array.from({length:n},(_,i)=>cyc(k,i,k+i)),t=dot(w,w);
  ck(t>0n,"nonzero tangent anchor");
  const S=mat(n,n,(i,j)=>(i===j?t:0n)-w[i]*w[j]);
  let G=mat(n,n,()=>0n);
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    const v=Array.from({length:n},(_,h)=>h===i?w[j]:h===j?-w[i]:0n);
    G=plus(G,rankone(v));
  }
  ck(eq(G,S),"PSD tangency represented by a Gram sum");
  ck(S.every(row=>dot(row,w)===0n),"zero direction in tangent matrix");
  const i=w.findIndex(x=>x!==0n);
  const minor=S.filter((_,j)=>j!==i).map(row=>row.filter((_,j)=>j!==i));
  ck(i>=0&&determinant(minor)===t**BigInt(n-2)*w[i]*w[i],
     "tangent has only one lost direction");
}
function determinant(X){
 const A=X.map(r=>r.slice()),n=A.length; let d=1n, s=1n;
 if(n===0)return 1n;
 for(let j=0;j<n-1;j++){
   let p=j;while(p<n&&A[p][j]===0n)++p;
   if(p===n)return 0n;
   if(p!==j){const tmp=A[j];A[j]=A[p];A[p]=tmp;s=-s;}
   const e=A[j][j];
   for(let i=j+1;i<n;i++)for(let h=j+1;h<n;h++){
     const v=e*A[i][h]-A[i][j]*A[j][h];
     if(v%d!==0n)throw new Error("fraction-free determinant division");
     A[i][h]=v/d;
   }
   for(let i=j+1;i<n;i++)A[i][j]=0n;
   d=e;
 }
 return s*A[n-1][n-1];
}
for(let n=2;n<=12;n++)for(let m=1;m<n;m++)for(let w=1;w<=48;w++){
  const A=gram(mat(n,m,(i,j)=>cyc(i,j,w+i)));
  const sub=mat(m+1,m+1,(i,j)=>A[i][j]);
  ck(determinant(sub)===0n,"low-rank determinant annihilator");
}
for(let d=1;d<=10;d++)for(let w=0;w<63;w++)for(let a=-4;a<=4;a++)for(let b=-3;b<=3;b++){
  const a0=BigInt(a),b0=BigInt(b),c=1n,D=2n;
  const v=Array.from({length:d*2},(_,i)=>cyc(w,i,w+i));
  for(let j=0;j<d;j++){
    const x=v[2*j],y=v[2*j+1],u=a0*x+b0*(x-y),z=a0*y+b0*(x+y);
    ck(u*u+z*z===(x*x+y*y)*(a0*a0+2n*c*a0*b0+D*b0*b0),"block norm of quadratic integer");
  }
}
for(let a=1;a<=9;a++)for(let b=1;b<=6;b++){
 const count=new Map(), M=43;
 for(let i=-M;i<=M;i++)for(let j=-M;j<=M;j++){
   const z=a*i*i+b*j*j;
   count.set(z,(count.get(z)??0)+1);
 }
 const all=(2*M+1)**2, pairs=[...count.values()].reduce((s,x)=>s+x*x,0);
 ck(count.size*pairs>=all*all,"Cauchy bound on distinct values");
 ck(count.get(0)===1,"positive definite zero value");
}
// Distinct rational coefficient pairs encode equal values of Q1+sqrt(2) Q2.
for(let a=1;a<=8;a++)for(let b=1;b<=6;b++){
 const count=new Map();
 for(let i=-45;i<=45;i++)for(let j=-45;j<=45;j++){
  const A=a*i*i+b*j*j,B=i*j, key=A+","+B;
  count.set(key,(count.get(key)??0)+1);
 }
 ck(Math.max(...count.values())<=4,"at most four representations in irrational metric");
}
console.log(tests+" exact matrix, lattice and binary-form checks: PASS");
