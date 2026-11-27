'use strict';
// Exact arithmetic in small cyclotomic examples. No sampler or lattice solver.
let checks=0;
const ok=x=>{checks++;if(!x)throw Error('identity failed')};
const gcd=(a,b)=>b?gcd(b,a%b):a;
for(let l=1;l<=32;l++)for(const sign of [1,-1]){
 const orders=Array.from({length:l},(_,k)=>sign===1?l/gcd(l,k):2*l/gcd(2*l,2*k+1));
 const one=new Set(orders);
 ok((one.size===1)===(sign===1?l===1:(l&(l-1))===0));
 if(one.size===1)ok(orders[0]===(sign===1?1:2*l));
}
function arr(d,v=[]){return Array.from({length:d},(_,i)=>v[i]||0);}
function mul(a,b){const d=a.length,r=arr(d);a.forEach((v,i)=>b.forEach((w,j)=>r[(i+j)%d]+=(i+j<d?1:-1)*v*w));return r;}
function con(a){return a.map((v,i)=>i?-a[a.length-i]:v);}
function add(a,b){return a.map((v,i)=>v+b[i]);}
function H(a,b){return a.reduce((t,x,i)=>add(t,mul(x,con(b[i]))),arr(a[0].length));}
function same(a,b){return a.every((x,i)=>x===b[i]);}
for(const d of [2,4,8,16]){
 const e=i=>Array.from({length:d},(_,j)=>Number(i===j));
 const u=e(0).map((x,i)=>x-e(d/2)[i]);
 ok(same(mul(u,con(u)),arr(d,[2])));
 ok(same(mul(u,u),e(d/2).map(x=>-2*x)));
 const v=[[e(0),e(1)],[e(0),e(1).map(x=>-x)]];
 const axes=v.flatMap(z=>Array.from({length:d},(_,i)=>z.map(x=>mul(x,e(i)))));
 for(let i=0;i<axes.length;i++)for(let j=0;j<axes.length;j++)
  ok(H(axes[i],axes[j])[0]*d===(i===j?2*d:0));
}
for(const G of [[[2,0],[0,5]],[[2,-1],[-1,2]],[[3,2],[2,3]]]){
 const E=(x,y)=>{const a=2*x-1,b=2*y+3;return G[0][0]*a*a+2*G[0][1]*a*b+G[1][1]*b*b};
 ok(E(1,1)+E(0,0)-E(1,0)-E(0,1)===8*G[0][1]);
}
console.log({exactChecks:checks});
