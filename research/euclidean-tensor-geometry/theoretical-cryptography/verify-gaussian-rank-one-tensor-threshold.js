'use strict';
const assert=require('node:assert/strict');
let exact=0,numeric=0;
function chk(b,m){assert(b,m);exact++;}
function near(a,b,t=1e-10){assert(Math.abs(a-b)<=t&&Number.isFinite(a),[a,b,t].join(' '));numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const pairs=n=>seq(n).flatMap(i=>seq(i).map(j=>[j,i]));
const choose=(n,k)=>k<0||n<k?0:k===0?1:choose(n-1,k-1)*n/k;
const pop=x=>{let n=0;for(;x;x&=x-1n)n++;return n;};
const dot=(a,b)=>a.reduce((s,v,i)=>s+v*b[i],0n);
function rects(p,q){
  return pairs(p).flatMap(([i,k])=>pairs(q).map(([j,l])=>{
    const mask=[i*q+j,i*q+l,k*q+j,k*q+l].reduce((u,b)=>u|(1n<<BigInt(b)),0n);
    return {mask,rows:(1n<<BigInt(i))|(1n<<BigInt(k)),cols:(1n<<BigInt(j))|(1n<<BigInt(l)),i,k,j,l};
  }));
}
for(let p=2;p<=6;p++)for(let q=2;q<=6;q++){
  const rs=rects(p,q),n=rs.length,groups=new Map();
  let ans=81n*BigInt(n), four=0;
  for(let j=0;j<n;j++)for(let i=0;i<j;i++){
    ans+=6n*3n**BigInt(pop(rs[i].mask&rs[j].mask));
    const key=rs[i].mask^rs[j].mask, prev=groups.get(key)??[];
    for(const [a,b] of prev) {
      chk(a!==i&&a!==j&&b!==i&&b!==j);
      const fourRs=[rs[i],rs[j],rs[a],rs[b]];
      const r=pop(fourRs.reduce((s,e)=>s|e.rows,0n)), c=pop(fourRs.reduce((s,e)=>s|e.cols,0n));
      chk(r<=4&&c<=4&&(r<=3||c<=3));
      four++;
    }
    prev.push([i,j]);groups.set(key,prev);
  }
  chk(four%3===0);
  ans+=24n*BigInt(four/3);
  chk(ans>=3n*BigInt(n)**2n);
  if(p<=4&&q<=4){
    let brute=0n;
    for(let a=0;a<n;a++)for(let b=a;b<n;b++)for(let c=b;c<n;c++)for(let d=c;d<n;d++){
      const masks=[rs[a].mask,rs[b].mask,rs[c].mask,rs[d].mask];
      if((masks[0]^masks[1]^masks[2]^masks[3])!==0n)continue;
      const same4=masks[0]&masks[1]&masks[2]&masks[3];
      const mult=a===d?1:(a===c||b===d)?4:(a===b&&c===d)?6:(a===b||b===c||c===d)?12:24;
      brute+=BigInt(mult)*3n**BigInt(pop(same4));
    }
    chk(brute===ans);
  }
}
function wick(row,S){
  if(row.length===0)return 1n;
  if(row.length%2)return 0n;
  let sum=0n;
  for(let j=1;j<row.length;j++)sum+=S[row[0]][row[j]]*wick(row.slice(1,j).concat(row.slice(j+1)),S);
  return sum;
}
function addRect(M,R){
  (M.get(R.j)??(M.set(R.j,[]),M.get(R.j))).push(R.i,R.k);
  (M.get(R.l)??(M.set(R.l,[]),M.get(R.l))).push(R.i,R.k);
}
for(let p=2;p<=5;p++)for(let q=2;q<=5;q++){
  const rs=rects(p,q),ix=seq(p),rowPairs=pairs(p),nq=BigInt(choose(q,2));
  for(let seed=0;seed<7;seed++){
    const A=ix.map(i=>ix.map(j=>BigInt((1103+i*j*(seed+2)+51*i+37*j+3*seed)%19-9)));
    const S=A.map((a,i)=>A.map((b,j)=>dot(a,b)+BigInt(i===j)));
    const v=rowPairs.map(([i,k])=>S[i][k]);
    const K=rowPairs.map(([i,k])=>rowPairs.map(([a,b])=>S[i][a]*S[k][b]+S[i][b]*S[k][a]));
    const targetMean=nq*dot(v,v), qn=BigInt(q);
    const targetVariance=qn*(qn-1n)**2n*dot(v,K.map(a=>dot(a,v)))+nq*K.reduce((a,b)=>a+dot(b,b),0n);
    let exp1=0n,exp2=0n;
    for(const R of rs){
      exp1+=S[R.i][R.k]**2n;
      for(const P of rs){
        const M=new Map();
        addRect(M,R);addRect(M,P);
        exp2+=Array.from(M.values()).reduce((u,row)=>u*wick(row,S),1n);
      }
    }
    chk(exp1===targetMean);
    chk(exp2-exp1**2n===targetVariance);
  }
}
function eg(m){let u=1n;for(let j=1;j<m;j+=2)u*=BigInt(j);return m%2?0n:u;}
function rawInnerProducts(edgeList,r){
  // Expand products of Gaussian row inner products in r independent inner indices.
  const counts=new Int16Array(5*r);
  function walk(j){
    if(j===edgeList.length){
      return counts.reduce((a,b)=>a*eg(b),1n);
    }
    const [a,b]=edgeList[j];let z=0n;
    for(let k=0;k<r;k++){
      counts[a*r+k]++;counts[b*r+k]++;
      z+=walk(j+1);
      counts[a*r+k]--;counts[b*r+k]--;
    }
    return z;
  }
  return walk(0);
}
for(let r=1;r<=16;r++){
  const L=BigInt(r),a=[0,1];
  chk(rawInnerProducts([a,a],r)===L);
  chk(rawInnerProducts([a,a,a,a],r)===3n*L*(L+2n));
  chk(rawInnerProducts([a,a,[0,2],[0,2]],r)===L*(L+2n));
  chk(rawInnerProducts([a,a,[2,3],[2,3]],r)===L**2n);
}
function gammaHalf(k){
 let z=k%2?Math.sqrt(Math.PI):1,n=k%2?0.5:1;
 for(;n<k/2;n++)z*=n;
 return z;
}
function simpson(f,lo,hi,N=4096){
  let s=f(lo)+f(hi),a=(hi-lo)/N;
  for(let j=1;j<N;j++)s+=(j%2?4:2)*f(lo+j*a);
  return a*s/3;
}
// Compare the interior likelihood-crossing formula to direct radial L1 integration.
for(const D of [1,2,3,6,10,15,21,28,36,45,55])for(const la of [0.02,0.065,0.2,0.8,2.3,5]){
  const G=gammaHalf(D),normalizer=2**(1-D/2)/G;
  const radial=(x,s)=>normalizer*x**(D-1)*Math.exp(-x*x/(2*s))/s**(D/2);
  const t=D*(1+la)*Math.log1p(la)/la,r=Math.sqrt(t);
  near(radial(r,1),radial(r,1+la));
  const cdf=t=>simpson(x=>radial(x,1),0,Math.sqrt(t));
  const f=cdf(t)-cdf(t/(1+la));
  const g=x=>Math.abs(radial(x,1)-radial(x,1+la));
  const l1=(simpson(g,0,r)+simpson(g,r,Math.sqrt(10*(D+55)*(1+la))))/2;
  near(f,l1,1e-9);
}
// Verify the conditional trace correction and determinant overlap identity
// on generated symmetric matrices with rational width entries.
const del=(i,j)=>BigInt(i===j);
const diag=(p,t)=>seq(p).map(i=>seq(p).map(j=>t*del(i,j)));
const matadd=(A,B)=>A.map((r,i)=>r.map((v,j)=>v+B[i][j]));
const matneg=A=>A.map(r=>r.map(z=>-z));
const matsc=(A,t)=>A.map(r=>r.map(x=>x*t));
const matmp=(A,B)=>A.map(r=>B[0].map((_,j)=>dot(r,B.map(v=>v[j]))));
const trace=A=>A.reduce((r,v,i)=>r+v[i],0n);
function detInt(M){
  if(M.length===1)return M[0][0];
  let z=0n;
  for(let j=0;j<M.length;j++)if(M[0][j]!==0n)
    z+=(j%2?-1n:1n)*M[0][j]*detInt(M.slice(1).map(r=>r.filter((_,k)=>k!==j)));
  return z;
}
for(let p=1;p<=8;p++)for(let h=0;h<21;h++){
 const z=seq(p), X=z.map(i=>z.map(j=>BigInt((i*j*(h+3)+7*(i+j)+h+5)%17-8)));
 const EXQ=z.map(i=>z.map(j=>z.reduce((r,k)=>r+z.reduce((t,l)=>
   t+X[k][l]*(del(i,l)*del(k,j)+del(i,j)*del(k,l)),0n),0n)));
 for(const i of z)for(const j of z)chk(EXQ[i][j]===X[i][j]+trace(X)*del(i,j));
 chk(trace(matmp(X,EXQ))===trace(matmp(X,X))+trace(X)**2n);
 const A=z.map(i=>z.map(j=>BigInt((i*5+j*7+h*i)%11-5)));
 const B=z.map(i=>z.map(j=>BigInt((i*11+j*5+h*j)%13-6)));
 const S=A.map((u,i)=>A.map((v,j)=>dot(u,v)+121n*del(i,j)));
 const R=B.map((u,i)=>B.map((v,j)=>dot(u,v)+121n*del(i,j)));
 const U=matadd(S,diag(p,-200n)),V=matadd(R,diag(p,-200n));
 const left=matadd(diag(p,40000n),matneg(matmp(U,V)));
 const right=matadd(matsc(matadd(S,R),200n),matneg(matmp(S,R)));
 chk(left.every((r,i)=>r.every((v,j)=>v===right[i][j])));
 if(p<=5)chk(detInt(left)===detInt(right));
}
function det2(A){return A[0][0]*A[1][1]-A[0][1]**2;}
function inv2(A){const u=det2(A);return [[A[1][1]/u,-A[0][1]/u],[-A[0][1]/u,A[0][0]/u]];}
function numericIntegral2(A){
 const R=10,d=0.05,N=Math.round(2*R/d);
 let total=0;
 for(let i=0;i<N;i++)for(let j=0;j<N;j++){
   const x=-R+(i+0.5)*d,y=-R+(j+0.5)*d;
   total+=Math.exp(-(A[0][0]*x*x+2*A[0][1]*x*y+A[1][1]*y*y)/2);
 }
 return total*d*d;
}
for(let h=0;h<13;h++){
 const S=[[0.91+0.01*h,0.02-h/500],[0.02-h/500,1.08-h/750]];
 const R=[[1.11-h/200,-0.04+h/700],[-0.04+h/700,0.92+h/180]];
 const U=S.map((r,i)=>r.map((x,j)=>x-(i===j?1:0)));
 const V=R.map((r,i)=>r.map((x,j)=>x-(i===j?1:0)));
 const UV=U.map(r=>[r[0]*V[0][0]+r[1]*V[1][0],r[0]*V[0][1]+r[1]*V[1][1]]);
 const D=(1-UV[0][0])*(1-UV[1][1])-UV[0][1]*UV[1][0];
 const J=inv2(S).map((r,i)=>r.map((x,j)=>x+inv2(R)[i][j]-(i===j?1:0)));
 near(numericIntegral2(J)/(2*Math.PI*Math.sqrt(det2(S)*det2(R))),D**(-0.5),3e-12);
}

console.log('PASS: '+exact+' exact and '+numeric+' numerical checks');
