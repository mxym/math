#!/usr/bin/env node
// Exact mixed Bernstein--Gram chart replay. Standard Node, no external packages.
// All sign decisions use bounded exact integers; division for estimating a proposed
// multiplier is not itself used as proof.
'use strict';
const zlib=require('node:zlib');
function gcd(x,y){if(x<0n)x=-x;if(y<0n)y=-y;while(y){let t=x%y;x=y;y=t;}return x;}
function R(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('zero denominator');if(d<0n){n=-n;d=-d;}const z=gcd(n,d);return [n/z,d/z];}
const Z=R(0),O=R(1),add=(x,y)=>R(x[0]*y[1]+x[1]*y[0],x[1]*y[1]),mul=(x,y)=>R(x[0]*y[0],x[1]*y[1]),neg=x=>[-x[0],x[1]],cmp=(x,y)=>x[0]*y[1]-x[1]*y[0], show=x=>x.join('/');
const P=(k=0,c=O)=>c[0]?new Map([[k,c]]):new Map();
function put(A,k,v){if(!v[0])return;const c=add(A.get(k)||Z,v);if(c[0])A.set(k,c);else A.delete(k);}
function plus(A,B){const C=new Map(A);for(const [k,b]of B)put(C,k,b);return C;}
function scale(A,b){const C=P(0,Z);for(const [k,v]of A)put(C,k,mul(v,b));return C;}
function prod(A,B){const C=P(0,Z);for(const[i,a]of A)for(const[j,b]of B)put(C,i+j,mul(a,b));return C;}
const sum=(...A)=>A.reduce(plus,P(0,Z)),diff=(A,B)=>plus(A,scale(B,R(-1))),a=P(1),b=P(32),c=P(1024);
function bases(x,k){const p=[P(),x];for(let j=2;j<=k;j++)p.push(diff(scale(prod(x,p[j-1]),R(2)),p[j-2]));return p;}
function lin(u,p){return sum(...u.map((v,i)=>scale(p[i],v)));}
const enc=(i,j,k)=>i+32*j+1024*k,idx=v=>[v%32,(v>>5)%32,v>>10];
function build(data,ep,et){
 const[n,q,d,D,h,g,B,fac]=data,den=BigInt(D),ch=bases(a,g.length),chb=bases(b,d),ab=prod(a,b),w=diff(c,ab),z=prod(diff(P(),prod(a,a)),diff(P(),prod(b,b))),Q=[P(),w];
 if(h.some(x=>x<0)||fac.length!==d+1)throw Error('not a positive kernel');
 for(let k=1;k<d;k++)Q.push(scale(diff(scale(prod(w,Q[k]),R(2*k+n-3)),scale(prod(z,Q[k-1]),R(k))),R(1,k+n-3)));
 let K=P(0,Z);for(let k=0;k<=d;k++){const M=fac[k];if(M.length!==d+1-k||M.some(r=>r.length!==M[0].length))throw Error('factor dimensions');let S=P(0,Z);
  for(let j=0;j<M[0].length;j++){const u=M.map(r=>R(r[j],den));S=plus(S,prod(lin(u,ch),lin(u,chb)));}K=plus(K,prod(S,Q[k]));}
 let H=P(0,Z);for(const[e,v]of K){const[i,j,k]=idx(e),u=mul(v,R(1,3));for(const ee of [e,enc(j,k,i),enc(k,i,j)])put(H,ee,u);}
 const gp=lin(g.map(x=>R(x,den)),ch);let T=diff(P(0,ep),H);for(const[i,v]of gp)for(const e of [i,i*32,i*1024])put(T,e,v);
 const cc=[P(),a];for(let k=1;k<h.length;k++)cc.push(scale(diff(scale(prod(a,cc[k]),R(2*k+n-2)),scale(cc[k-1],R(k))),R(1,k+n-2)));
 const hp=lin(h.map(x=>R(x,den)),cc.slice(1)),aa=prod(a,a),f=diff(prod(aa,aa),scale(aa,R(1,4)));let H11=P(0,Z),H111=Z;
 for(const[e,v]of H){const[i,j,k]=idx(e);put(H11,j+k,v);H111=add(H111,v);}
 const Y=diff(P(0,add(R(B,den),et)),sum(f,hp,scale(H11,R(3)),scale(gp,R(3*(q-2)))));
 const energy=[R(3,4),R(h.reduce((v,w)=>v+BigInt(w),0n),den),H111,mul(R(q-1),add(R(B,den),et)),mul(R((q-1)*(q-2)),ep)].reduce(add,Z);
 return [T,Y,energy];
}
function choose(n,k){if(k<0||k>n)return 0n;let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-i+1)/BigInt(i);return x;}
function divfloor(x,d){let z=x/d;return x<0n&&x%d?z-1n:z;}
function bern(A,dim,up=false,force=null){
 const ds=force?force.slice():Array(dim).fill(0);for(const i of A.keys())idx(i).slice(0,dim).forEach((v,j)=>ds[j]=Math.max(ds[j],v));const stride=ds.map((_,j)=>ds.slice(0,j).reduce((s,n)=>s*(n+1),1)),L=ds.reduce((s,n)=>s*(n+1),1),v=Array(L).fill(Z);
 for(const[i,r]of A){const I=idx(i);if(I.slice(dim).some(x=>x))throw Error('nonunivariate');v[I.slice(0,dim).reduce((s,n,k)=>s+n*stride[k],0)]=r;}
 let V=v;
 for(let k=0;k<dim;k++){const d=ds[k],s=stride[k],W=V.slice(),T=Array.from({length:d+1},(_,i)=>Array.from({length:d+1},(_,j)=>{let f=Z;for(let t=0;t<=Math.min(i,j);t++)f=add(f,R(choose(j,t)*choose(i,t)*BigInt((j-t)%2?-1:1)*3n**BigInt(t),choose(d,t)*2n**BigInt(t)));return f;}));
  for(let i=0;i<L;i++){const t=Math.floor(i/s)%(d+1),base=i-t*s;let x=Z;for(let j=0;j<=d;j++)if(V[base+j*s][0]&&T[t][j][0])x=add(x,mul(T[t][j],V[base+j*s]));W[i]=x;}V=W;
 }
 const gg=Float64Array.from(V,r=>{const n=r[0]*(1n<<34n),v=up?-divfloor(-n,r[1]):divfloor(n,r[1]);if(v>2n**50n||v< -(2n**50n))throw Error('dyadic guard');return Number(v);});return {A:gg,ds,stride,L};
}
function split(V,k,up){const {A,ds,stride,L}=V,s=stride[k],d=ds[k],W=new Float64Array(L),Zz=new Float64Array(L),u=new Float64Array(d+1);
 for(let h=0;h<L;h+=s*(d+1))for(let b=0;b<s;b++){const base=h+b;for(let j=0;j<=d;j++)u[j]=A[base+j*s];W[base]=u[0];Zz[base+d*s]=u[d];for(let j=1;j<=d;j++){
  for(let i=0;i<=d-j;i++){const t=(u[i]+u[i+1])/2;u[i]=up?Math.ceil(t):Math.floor(t);}W[base+j*s]=u[0];Zz[base+(d-j)*s]=u[d-j];}}
 return [{...V,A:W},{...V,A:Zz}];
}
function check(V,G){const dim=V.ds.length;let nodes=0,close=0,out=0;
 function go(U,Q,lo,hi,d){
  nodes++;if(nodes>9000000||d>78)throw Error('unresolved Bernstein box');
  if(lo.some((v,i)=>i<dim-1&&v>hi[i+1])){out++;return;}
  if(U.A.every(x=>x>=0)){close++;return;}
  if(Q){
   if(Q.A.every(v=>v<0)){out++;return;}
   if(Q.A.every(v=>v>=0))Q=null;
   else{
    let lb=0,ub=Infinity;const ua=U.A,qa=Q.A;for(let i=0;i<ua.length;i++){let x=ua[i],y=qa[i];if(y>0)ub=Math.min(ub,x/y);else if(y<0)lb=Math.max(lb,x/y);else if(x<0){ub=-1;break;}if(lb>ub)break;}
    if(lb>0&&ub>=lb){
     const p=2**(Math.floor(Math.log2(lb))-16),a=Math.ceil(lb/p);if(a*p<=ub&&Number.isSafeInteger(a)&&qa.every((v,i)=>Number.isSafeInteger(v*a)&&ua[i]>=(v*a)*p)){close++;return;}
    }
   }
  }
  const k=d%dim,[l,r]=split(U,k,false),[p,q]=Q?split(Q,k,true):[null,null],mid=(lo[k]+hi[k])/2,h=hi.slice(),a=lo.slice();h[k]=mid;a[k]=mid;go(l,p,lo,h,d+1);go(r,q,a,hi,d+1);
 }
 go(V,G,Array(dim).fill(0),Array(dim).fill(1),0);return {nodes,close,out};
}
const determinant=sum(P(),scale(prod(prod(a,b),c),R(2)),scale(sum(prod(a,a),prod(b,b),prod(c,c)),R(-1)));


function corrected(C,sl){
 const [T,Y,U]=build(C,Z,Z),q=C[1],V=plus(scale(T,R(3*(q-2))),P(0,mul(R(3),sl)));for(const[i,v]of Y){for(const k of[i,32*i,1024*i])put(V,k,v);}
 const gam=R(17,100),r=R(-881,1000),gg=[a,b,c].map(t=>{const z=prod(t,t);return diff(prod(z,z),scale(z,R(1,4)));});let W=V;
 for(const z of gg)W=plus(W,plus(scale(z,mul(R(2),mul(gam,r))),scale(prod(z,z),gam)));
 for(let i=0;i<3;i++)W=plus(W,scale(prod(gg[i],gg[(i+1)%3]),mul(gam,R(q-2))));
 const vv=bern(W,3),cc=check(vv,bern(determinant,3,true,vv.ds));return [add(add(U,mul(R(q-1),sl)),neg(mul(gam,mul(r,r)))),cc];
}


function direct(C,sl){
 const [T,Y,U]=build(C,Z,Z),q=C[1],V=plus(scale(T,R(3*(q-2))),P(0,mul(R(3),sl)));for(const[i,v]of Y){for(const k of[i,32*i,1024*i])put(V,k,v);}
 const vv=bern(V,3),c=check(vv,bern(determinant,3,true,vv.ds));return [add(U,mul(R(q-1),sl)),c];
}


const cards=["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"].map(x=>JSON.parse(zlib.inflateSync(Buffer.from(x,'base64'))));
function req(x,s){if(!x)throw Error(s);}
const want=['1632126774274021/1000000000000000','3277822550304317/2000000000000000'];
const expected=[[1425,583,130],[1787,737,157]];
for(let i=0;i<2;i++){
 const c=cards[i];req((c[0]===6)&&(c[1]===(i===0?27:29)), 'incorrect row parameters');
 req(c[3]>0&&c[4].every(Number.isSafeInteger)&&c[5].every(Number.isSafeInteger)&&c[7].every(m=>m.every(v=>v.every(Number.isSafeInteger))),'integer factors');
 const [r,b]=(i===0?corrected:direct)(c,R(1,200000)); req(show(r)===want[i],'rational mismatch');
 req([b.nodes,b.close,b.out].every((a,j)=>a===expected[i][j]),'box census');
 console.log('PASS',c[1],show(r),b);
}
const prev=R(652948043974739,400000000000000),B0=R(1631,1000),gamma=R(17,100),U=R(16321271,10000000);
const d0=add(prev,neg(B0));req(cmp(d0,Z)>0n&&cmp(U,B0)>0n&&cmp(U,add(R(1632126774274021,1000000000000000),mul(gamma,mul(d0,d0))))>0n,'variance bootstrap');
req(cmp(mul(U,R(16542829,1000000)),R(27))<=0n&&cmp(mul(R(3277822550304317,2000000000000000),R(17694673,1000000)),R(29))<=0n,'charge rounding');
console.log('PASS weighted/uniform charges >=16.542829,17.694673');
