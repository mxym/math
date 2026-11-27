"use strict";
// Exact finite checks for the shared-multiplier theorem.
// All examples use synthetic uniform scalar label arrays.
let checks=0;
function eq(a,b,msg){checks++;if(a!==b)throw Error(msg+": "+a+" != "+b);}
function assert(x,msg){eq(Boolean(x),true,msg);}
function vectors(q,m){
  let result=[[]];
  for(let i=0;i<m;i++)result=result.flatMap(xs=>Array.from({length:q},(_,v)=>[...xs,v]));
  return result;
}
const key=(q,xs)=>xs.reduce((z,x)=>q*z+x,0);
function product(T,U,n,r,m,q){
  const Y=Array(n*m).fill(0);
  for(let j=0;j<m;j++)for(let a=0;a<r;a++)for(let i=0;i<n;i++)
    Y[j*n+i]=(Y[j*n+i]+T[a*n+i]*U[j*r+a])%q;
  return Y;
}
function imCard(Y,p,d,n,m,power){
  const q=p**d,coefv=vectors(q,m),B=new Set();
  for(const v of coefv){
    const s=Array(n).fill(0);
    for(let j=0;j<m;j++)for(let i=0;i<n;i++)s[i]=(s[i]+p**power*v[j]*Y[j*n+i])%q;
    B.add(key(q,s));
  }
  return B.size;
}
function shape(Y,p,d,n,m){
  const k=[];let last=imCard(Y,p,d,n,m,0);
  for(let j=1;j<=d;j++){
    const next=j===d?1:imCard(Y,p,d,n,m,j);
    let ratio=last/next,dim=0;
    while(ratio>1){ratio/=p;dim++;}
    k.push(dim);last=next;
  }
  return k;
}
function gb(n,r,p){
  if(r<0||r>n)return 0n;
  if(r===0||r===n)return 1n;
  return gb(n-1,r-1,p)+BigInt(p)**BigInt(r)*gb(n-1,r,p);
}
function contains(k,p,d,n,r){
  if(k[0]>r)return 0n;
  const a=k.slice(1).reduce((x,y)=>x+y,0);
  return gb(n-k[0],r-k[0],p)*BigInt(p)**BigInt((n-r)*((d-1)*r-a));
}
function countType(k,p,d,n,m){
  if(k[0]>m)return 0n;
  let B=1n;
  for(let j=0;j<d;j++){
    const next=k[j+1]||0;
    B*=BigInt(p)**BigInt((n-k[j])*next)*gb(n-next,k[j]-next,p);
  }
  const l=k.reduce((x,y)=>x+y,0);
  B*=BigInt(p)**BigInt(m*(l-k[0]));
  for(let i=0;i<k[0];i++)B*=BigInt(p)**BigInt(m)-BigInt(p)**BigInt(i);
  return B;
}
function test(p,d,n,r,m){
  const q=p**d, Ts=vectors(q,n*r),Us=vectors(q,r*m),Ys=vectors(q,n*m);
  const Tstar=Ts.filter(T=>imCard(T.map(x=>x%p),p,1,n,r,0)===p**r);
  const P=Array(Ys.length).fill(0);
  for(const T of Tstar)for(const U of Us)P[key(q,product(T,U,n,r,m,q))]++;
  const den=BigInt(Tstar.length*Us.length),N=BigInt(Ys.length);
  const nb=BigInt(p)**BigInt((d-1)*r*(n-r))*gb(n,r,p),nr=BigInt(q)**BigInt(r*m);
  let excess=0n, mass=0n;const event=new Set(), typeCounts=new Map();
  for(let id=0;id<Ys.length;id++){
    const k=shape(Ys[id],p,d,n,m),tag=k.join(",");
    typeCounts.set(tag,(typeCounts.get(tag)||0n)+1n);
    const cv=contains(k,p,d,n,r);
    eq(BigInt(P[id])*nb*nr,den*cv,"uniform summand likelihood");
    if(BigInt(P[id])*N>den){
      excess+=BigInt(P[id])*N-den;
      mass+=BigInt(P[id]);event.add(id);
    }
    if(m>=r+1 && k[0]<=r)assert(BigInt(P[id])*N>=den,"support domination");
  }
  for(const [type,size] of typeCounts)
    eq(size,countType(type.split(",").map(Number),p,d,n,m),"exact target type count");
  for(const T of Ts){
    let count=0;
    for(const U of Us)count+=event.has(key(q,product(T,U,n,r,m,q)));
    assert(BigInt(count)*BigInt(Tstar.length)>=mass,"monotone dual certificate for each fixed multiplier");
  }
  if(m===1){
    const pn=BigInt(p)**BigInt(n),pr=BigInt(p)**BigInt(r);
    eq(excess*pr*pn,den*N*(pn-pr),"one-label closed optimum");
  } else if(m>=r+1){
    eq(excess,den*BigInt(P.filter(x=>x===0).length),"support-bound attainment");
  }
}
for(const t of [[2,1,2,1,1],[2,1,2,1,3],[2,1,4,2,1],[2,1,4,2,2],[2,1,4,2,3],
  [3,1,3,2,2],[2,2,2,1,1],[2,2,2,1,3],[2,2,3,2,1],[2,2,3,2,2],
  [2,3,2,1,2],[3,2,2,1,2]])test(...t);
// Unramified quadratic toy quotient B=(Z/9)[x]/(x^2+1), conductor 3.
for(const [a,b] of vectors(9,2)){
  if(a%3===0&&b%3===0)continue;
  const mass=Array(81).fill(0);
  for(const [x,y] of vectors(9,2)){
    const u=((a*x-b*3*y)%9+9)%9,v=(b*x+a*3*y)%9;
    mass[u*9+v]++;
  }
  for(const [x,y] of vectors(9,2)){
    const inLine=[0,1,2].some(i=>(x-i*a)%3===0&&(y-i*b)%3===0);
    eq(mass[x*9+y],inLine?3:0,"upper digits fill the exact fiber");
  }
}
console.log("OK: "+checks+" exact type, likelihood, monotone-certificate and fiber checks.");
