'use strict';
const assert=require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;
const F=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(b<0n)[a,b]=[-a,-b];assert(b>0n);const g=gcd(a,b);return [a/g,b/g];};
const add=([a,b],[c,d])=>F(a*d+b*c,b*d), mul=([a,b],[c,d])=>F(a*c,b*d);
const inv=([a,b])=>F(b,a), neg=([a,b])=>F(-a,b), sub=(a,b)=>add(a,neg(b));
const div=(a,b)=>mul(a,inv(b)), pow=(a,n)=>n?mul(a,pow(a,n-1)):F(1);
const cmp=([a,b],[c,d])=>a*d-b*c;
const ex=(a,K=60)=>{
  let s=F(1),t=F(1);
  for(let i=1;i<=K;i++){t=div(mul(t,a),F(i));s=add(s,t);}
  t=div(mul(t,a),F(K+1));
  return [s,add(s,div(t,sub(F(1),div(a,F(K+2)))))];
};
const I=(a,b=a)=>[a,b], A=(a,b)=>[add(a[0],b[0]),add(a[1],b[1])];
const N=a=>[neg(a[1]),neg(a[0])], S=(a,b)=>A(a,N(b));
const M=(a,b)=>{assert(a[0][0]>=0n&&b[0][0]>=0n);return [mul(a[0],b[0]),mul(a[1],b[1])];};
const P=(a,k)=>[pow(a[0],k),pow(a[1],k)];
const C=(a,n)=>M(a,I(F(n)));
function reciprocal(a){assert(a[0][0]>0n);return [inv(a[1]),inv(a[0])];}
const rangeExp=a=>reciprocal(ex(a));
function H(a){
  const q=rangeExp(a), m=j=>{
    const x=mul(F(4**j),pow(q[1],3));
    return I(F(1),inv(sub(F(1),x)));
  };
  const b=M(C(q,2),reciprocal(A(I(F(1)),C(M(q,m(0)),2))));
  return A(S(S(C(m(2),15),M(I(mul(F(2),a)),m(3))),C(M(b,P(m(1),2)),45)),
    M(I(mul(F(30),a)),M(P(b,2),P(m(1),3))));
}
let exact=0,num=0;
const gt=(a,b)=>{assert(cmp(a,b)>0n);exact++;};
const lt=(a,b)=>gt(b,a);
gt(ex(F(157,50))[0],F(23));
gt(ex(F(5))[0],F(140));lt(ex(F(5))[1],F(150));
gt(ex(F(37,5))[0],F(1600));
gt(H(F(3737,500))[0],F(0));lt(H(F(299,40))[1],F(0)); // 7.474 and 7.475.
const tail=(j,B)=>F(4**j,B**3-4**j);
lt(mul(F(2,23),add(F(1),tail(1,23))),F(1,11));
lt(mul(F(74,5),tail(3,23)),F(79,1000));
lt(mul(F(90),pow(add(F(1),tail(1,23)),2)),F(91));
lt(mul(F(1260),add(F(1),tail(0,23))),F(1261));
lt(tail(4,1600),F(1,10000000));
const ss=F(1001,1000),bb=F(1,800);
const d=[mul(F(15),tail(4,1600)),mul(F(45),mul(bb,pow(ss,2))),
  mul(F(90),mul(bb,mul(ss,tail(2,1600)))),mul(F(30),mul(pow(bb,2),pow(ss,3)))].reduce(add,F(-2));
lt(d,F(0));
for(const a of [F(22,7),F(37,5)]){
  const den=cmp(a,F(37,5))===0n?1600:23;
  gt(sub(sub(sub(F(15),mul(F(2),a)),F(79,1000)),F(91,den)),F(0));
}
gt(sub(add(sub(mul(F(4),pow(F(22,7),2)),mul(F(56),F(22,7))),F(210)),F(1261,23)),F(0));
gt(sub(F(14),F(1261,140)),F(0));gt(F(1261,150),F(8));
function mg(t,k){
  const a=Array(k+1).fill(0);a[0]=1;
  const bound=Math.max(8,Math.ceil(Math.sqrt(72/t)));
  for(let n=1;n<=bound;n++){
    const w=2*Math.exp(-t*n*n);let p=w;
    for(let j=0;j<=k;j++){a[j]+=p;p*=n*n;}
  }
  return a.map(x=>x/a[0]);
}
const choose=(n,k)=>{let a=1;for(let i=1;i<=k;i++)a*=(n+1-i)/i;return a;};
const df=k=>k>0?(2*k-1)*df(k-1):1;
const surplus=(p,k)=>p[k]-df(k)*p[1]**k;
for(let i=0;i<=60;i++){
  const t=.43+i*.05, p=mg(t,4), sg=t<1.320411133?-1:1;
  assert(surplus(p,2)>0&&surplus(p,4)>0&&sg*surplus(p,3)>0);num+=3;
}
for(const k of [3,5]){
  const r=128,n=3;
  for(let j=n;j>=1;j--)for(const [t,sign] of [[.7,-1],[2,1]]){
    let moments=Array(k+1).fill(0);moments[0]=1;
    for(let i=1;i<=n;i++){
      const b=r**(i-j), p=mg(t*b,k).map((x,j)=>x*b**(2*j));
      moments=moments.map((_,l)=>p.slice(0,l+1).reduce((s,x,id)=>s+choose(2*l,2*id)*x*moments[l-id],0));
    }
    assert(sign*surplus(moments,k)>0);num++;
  }
}
console.log('PASS',exact,'exact rational bounds and',num,'numerical sanity checks');
