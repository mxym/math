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


function direct(C,sl){
 const [T,Y,U]=build(C,Z,Z),q=C[1],V=plus(scale(T,R(3*(q-2))),P(0,mul(R(3),sl)));for(const[i,v]of Y){for(const k of[i,32*i,1024*i])put(V,k,v);}
 const vv=bern(V,3),c=check(vv,bern(determinant,3,true,vv.ds));return [add(U,mul(R(q-1),sl)),c];
}

const data=JSON.parse(zlib.inflateSync(Buffer.from('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','base64')));
const nums=x=>Array.isArray(x)?x.flatMap(nums):[x];
if(data[0]!==6||data[1]!==25||data[2]!==13||data[4].length>30||data[5].length!==14||!nums(data).every(Number.isSafeInteger))throw Error('unexpected source row');
const [u,cells]=direct(data,R(1,75000));if(show(u)!=='4038635211584013/2500000000000000')throw Error('different energy');
const w=Number(25000000n*u[1]/u[0]);if(w!==15475524)throw Error('different charge');
const sums=[1333333+4975124+7329707+w+18892824,1333333+4975124+8527648+w+17692255];
if(sums.join(',')!=='48006512,48003884')throw Error('template budget');console.log('PASS U25',show(u),'cells',cells.nodes,'charge',w,'two excluded totals',sums.join(','));
