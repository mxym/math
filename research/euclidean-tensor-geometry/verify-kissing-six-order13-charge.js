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
const nums=x=>Array.isArray(x)?x.flatMap(nums):[x];if(data[0]!==6||data[1]!==13||data[2]!==13||data[4].length>30||data[5].length!==14||!nums(data).every(Number.isSafeInteger))throw Error('unexpected source row');
const [u,cells]=direct(data,R(1,75000));const charge=13000000n*u[1]/u[0];if(show(u)!=='7580247959364231/5000000000000000'||charge!==8574917n)throw Error('different claimed bound');console.log('PASS order 13',show(u),cells.nodes,'cells; charge',charge.toString());