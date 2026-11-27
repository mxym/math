"use strict";

// Deterministic finite circulations, characters and phase integrals.
let exact=0,numeric=0;
function chk(v,m){ if(!v)throw new Error(m); ++exact; }
function near(a,b,e,m){
 if(!Number.isFinite(a)||!Number.isFinite(b)||Math.abs(a-b)>e*Math.max(1,Math.abs(a),Math.abs(b)))
  throw new Error(m+": "+a+" vs "+b);
 ++numeric;
}
const key=z=>z.join(",");
function perm(n,j) {
 const ans=[],v=[]; const walk=used=>{
  if(v.length===j){ans.push(v.slice());return;}
  for(let i=0;i<n;i++)if((used&(1<<i))===0){v.push(i);walk(used|(1<<i));v.pop();}
 };
 walk(0);return ans;
}
const sq=z=>z.reduce((x,b)=>x+b*b,0);
const add=(x,y)=>x.map((a,i)=>a+y[i]);
const neg=x=>x.map(y=>-y);
function falling(n,r){let y=1;for(let i=0;i<r;i++)y*=n-i;return y;}
function cycles(p,q,k) {
 const a=perm(p,k),b=perm(q,k),ans=[];
 for(const u of a){
  if(u[0]!==Math.min(...u))continue;
  for(const v of b){
   const z=new Array(p*q).fill(0);
   for(let i=0;i<k;i++) { z[u[i]*q+v[i]]++; z[u[(i+1)%k]*q+v[i]]--; }
   ans.push(z);
  }
 }
 return ans;
}
function balanced(p,q,z) {
 for(let i=0;i<p;i++)if(z.slice(i*q,(i+1)*q).reduce((a,b)=>a+b,0)!==0)return false;
 for(let j=0;j<q;j++){
  let a=0;for(let i=0;i<p;i++)a+=z[i*q+j];if(a!==0)return false;
 }
 return true;
}
for(let p=2;p<=6;p++)for(let q=2;q<=6;q++)
for(let k=2;k<=Math.min(p,q);k++){
 const rs=cycles(p,q,k),set=new Set(rs.map(key));
 chk(rs.length===falling(p,k)*falling(q,k)/k,"oriented cycle count");
 chk(set.size===rs.length,"no repeated orientation");
 for(const z of rs){
  chk(balanced(p,q,z) && sq(z)===2*k,"oriented sum and energy");
  chk(set.has(key(neg(z))),"reverse orientation present");
  chk(set.has(key(neg(z)))&&!set.has(key(z.map(x=>2*x))),"pairing identity");
 }
}
function box(p,q,r,rec) {
 const z=new Array(p*q).fill(0);
 const f=(i,j)=>{
  if(i===p-1){
   for(let c=0;c<q;c++){let x=0;for(let h=0;h<p-1;h++)x+=z[h*q+c];z[i*q+c]=-x;}
   rec(z);return;
  }
  if(j===q-1){
   z[i*q+j]=-z.slice(i*q,i*q+j).reduce((a,b)=>a+b,0);
   f(i+1,0);return;
  }
  for(let k=-r;k<=r;k++){z[i*q+j]=k;f(i,j+1);}
 };
 f(0,0);
}
for(const [p,q,r] of [[2,3,3],[2,5,2],[3,3,2],[3,4,1],[4,4,1]]){
 const cs=[];for(let l=2;l<=Math.min(p,q);l++)cs.push(...cycles(p,q,l));
 let theta=0;
 box(p,q,r,v=>{
  chk(balanced(p,q,v),"row column constraint basis");
  const en=sq(v),l1=v.reduce((x,b)=>x+Math.abs(b),0);
  chk(l1<=en,"integer square at least absolute value");
  let w=v.slice(),s=0;
  while(w.some(x=>x)){
   const c=cs.find(x=>x.every((y,j)=>y===0||y*w[j]>0));
   if(!c)throw new Error("no conformal simple circuit");
   s+=sq(c); w=add(w,neg(c));
  }
  chk(l1===s,"conformal circuit decomposition");
  theta+=0.18**en;
 });
 const upper=cs.reduce((s,x)=>s/(1-0.18**sq(x)),1);
 chk(theta<=upper+1e-11,"finite theta under cycle multiset majorant");
}
for(const [p,q,r] of [[2,2,2],[2,3,2],[3,2,2],[3,3,1]]){
 const cts=new Array(21).fill(0),cts2=new Array(21).fill(0);
 box(p,q,r,v=>{
   let ok=true;
   for(let i=0;i<p;i++)for(let j=0;j<q;j++)if(Math.abs(v[i*q+j])>r)ok=false;
   if(ok&&sq(v)<cts.length)++cts[sq(v)];
 });
 const cols=[],z=new Array(p).fill(0);
 function f(j,s) {
  if(j===p-1){if(Math.abs(s)<=r){z[j]=-s;cols.push(z.slice());}return;}
  for(let k=-r;k<=r;k++){z[j]=k;f(j+1,s+k);}
 }
 f(0,0);
 function fold(j,v,en){
  if(en>=cts2.length)return;
  if(j===q){if(v.every(x=>x===0))++cts2[en];return;}
  for(const a of cols)fold(j+1,add(v,a),en+sq(a));
 }
 fold(0,new Array(p).fill(0),0);
 for(let j=0;j<cts.length;j++)chk(cts[j]===cts2[j],"balanced column coefficient");
}
const pi=Math.PI;
function circle(a,y){
 let z=1;
 for(let j=1;j<=12;j++)z+=2*a**(j*j)*Math.cos(2*pi*j*y);
 return z;
}
for(const p of [2,3,4])for(const a of [.04,.11,.23,.31])for(let k=1;k<=15;k++){
 const u=Array.from({length:p},(_,j)=>0.51*Math.sin((j+1)*(k+1)*1.34));
 let dir=0;
 for(let h=0;h<512;h++)dir+=u.reduce((v,x)=>v*circle(a,x+h/512),1)/512;
 let sum=0,F=0;
 for(let i=0;i<p;i++)for(let j=0;j<p;j++)if(i!==j)F+=Math.cos(2*pi*(u[i]-u[j]));
 const Z=new Array(p).fill(0);
 function go(i,x){
  if(i===p-1){
    if(Math.abs(x)>5)return;
    Z[i]=-x;
    const g=u.reduce((s,v,j)=>s+v*Z[j],0);
    sum+=a**sq(Z)*Math.cos(2*pi*g);return;
  }
  for(let j=-5;j<=5;j++){Z[i]=j;go(i+1,x+j);}
 }
 go(0,0);
 near(dir,sum,4e-12,"column phase average");
 near((dir-1)/a**2,F,80*a*a,"column leading Fourier shell");
}
for(const y of [.01,.1,.33,.67,.8,.93,.98]){
 let s=0;for(let j=2;j<=4096;j++)s+=y**j/j;
 near(Math.exp(s),Math.exp(-y)/(1-y),5e-13,"cycle logarithm series");
}
for(const tau of [.01,.25,.67,1.1,2.1])for(const Z of [[0,0],[.1,.3],[-.84,1.6],[.4,2.3]]){
 let theta=0;
 for(let i=0;i<2048;i++){
  const a=2*pi*i/2048;
  theta+=Math.exp(2*tau*(Math.cos(a)*Z[0]-Math.sin(a)*Z[1])-tau*tau)/2048;
 }
 const k=tau*tau*(Z[0]**2+Z[1]**2);
 let sum=1,v=1;
 for(let i=1;i<=60;i++){v*=k/i/i;sum+=v;}
 near(theta,Math.exp(-tau*tau)*sum,2e-12,"common-angle p=2 phase integral");
}
console.log(exact+" exact structural checks; "+numeric+
            " deterministic numerical checks: PASS");
