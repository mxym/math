'use strict';
const trim=a=>{while(a.length&&a.at(-1)===0)a.pop();return a};
const add=(a,b)=>trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||0)+(b[i]||0)));
const mul=(a,b)=>{let c=[];for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]=(c[i+j]||0)+a[i]*b[j];return trim(c)};
const xp=n=>Array(n).fill(0).concat(1);
const monDiv=(a,b)=>{a=a.slice();let q=Array(Math.max(0,a.length-b.length+1)).fill(0);while(a.length>=b.length){let p=a.length-b.length,r=a.at(-1);q[p]=r;for(let i=0;i<b.length;i++)a[i+p]-=r*b[i];trim(a)}return [trim(q),a]};
const phi=[null,[-1,1]];
for(let i=2;i<=18;i++){let a=xp(i);a[0]=-1;for(let j=1;j<i;j++)if(i%j===0){const [Q,R]=monDiv(a,phi[j]);if(R.length)throw Error('cyclotomic');a=Q;}phi.push(a)}
const P=[0,4,0,-5,0,1];
function rec(F){let r=F.length-1,G=[];for(let i=0;i<=r;i++){let n=1;for(let j=0;j<=i;j++){const k=r+i-2*j;G[k]=(G[k]||0)+F[i]*n;n=n*(i-j)/(j+1)}}return trim(Array.from({length:2*r+1},(_,i)=>G[i]||0));}

const mod=(x,p)=>(x%p+p)%p;
function norm(A,B){return A*A-A*B-B*B;} 
function cap(A,B){
 let D=Math.abs(norm(A,B));if(D<=1)return null;const poss=[[0,0]], used=new Set([0]),
 gen=[[A-B,-B],[-B,A]];
 for(let i=0;i<poss.length;i++)for(const [v,w] of gen){const [a,b]=poss[i],c=mod(a+v,D),d=mod(b+w,D),k=c*D+d;if(!used.has(k)){used.add(k);poss.push([c,d]);}}
 if(poss.length!==D)throw Error('characters');
 const g=x=>{x=mod(x,D);return 4*Math.min(x,D-x)>=D;};
 for(const [a,b] of poss)if(g(a))for(const [c,d] of poss)if(g(c)&&g(d-a)&&g(b+d)&&g(b-c))return {A,B,D,coeff:[a,b,c,d]};
 return null;
}

const assert=(ok,m)=>{if(!ok)throw Error(m)};
const checkPhi=(f,m,q)=>monDiv(f,phi[m])[1].every(x=>x%q===0);
const recTrace=(Q,s)=>rec(add(mul(P,Q),[s]));
assert(checkPhi(recTrace([1,1],1),5,2),'degree 12');
assert(checkPhi(recTrace([0,0,1],1),5,2),'degree 14 even');
assert(checkPhi(recTrace([1,1,1],1),9,2),'degree 14 odd');
for(const [c,d,m] of [[0,0,15],[1,0,9],[1,1,7]])
 assert(checkPhi(recTrace([d,d,c,1],1),m,2),'degree 16 nonexceptional parity');
const res=[], congruence={}, characters=[];
for(const s of [-1,1])for(let u=-199;u<=199;u++){
 if(!u)continue;
 const V=2*u*u-s*u;
 for(let v=1;v*v<=V;v+=2)if(v*v===V){
  for(let c=-300;c<=300;c+=2){
   const X=s-u-2,Y=3*u+1,Z=2*v-c,W=-2*c-v;
   const [A,B,A1,B1]=[X+Z,Y+W,X-Z,Y-W];
   let a=norm(A,B),b=norm(A1,B1);
   if(Math.abs(a)>1600||Math.abs(b)>1600)continue;
   const d=u-2,e=v-2*c,F=add(mul(P,[e,d,c,1]),[s]),f=rec(F);
   const R=monDiv(F,[-1,1,1])[1],T=monDiv(F.map((x,i)=>i%2?-x:x),[-1,1,1])[1];
   assert((R[0]||0)===A&&(R[1]||0)===B&&(T[0]||0)===A1&&(T[1]||0)===B1,'trace remainder');
   assert(a-b===10*((3*u+1)*c+(s-2-u)*v),'norm difference');
   assert(a+b===10*(u*u-v*c-c*c-(2*s-1)*u)+12-10*s,'norm sum');
   let known=[];
   for(const q of [2,3,5,7,11,13])for(const m of [5,7,9,10,12,18])
    if(checkPhi(f,m,q))known.push([m,q]);
   if(known.length){const k=known[0].join(',');congruence[k]=(congruence[k]||0)+1;continue;}
   const c5=cap(A,B), C=c5??cap(A1,B1);
   if(!C){res.push([s,u,v,c]);continue;}
   const {A:a0,B:b0,D,coeff:[r0,r1,t0,t1]}=C;
   for(const [p,q] of [[r0,r1],[t0,t1]])
    assert(mod(p*a0+q*b0,D)===0&&mod(p*b0+q*(a0-b0),D)===0,'character equations');
   let steps=[r0,t0,t1-r0,-r1-t1,r1-t0].map(a=>mod(a,D));
   assert(steps.every(x=>4*Math.min(x,D-x)>=D),'quarter-circle separation');
   characters.push({s,u,v,c,order:c5?5:10,D,labels:[r0,r1,t0,t1],steps});
  }
 }
}
assert(res.length===0&&Object.values(congruence).reduce((a,b)=>a+b,0)===19&&characters.length===19,
 'finite classification');
console.log(JSON.stringify({count:38,congruence,characters},null,2));
