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

const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const read=name=>fs.readFileSync(path.join(__dirname,name),'utf8');
function verifyCharts(data,only=null){
 const keys=Object.keys(data).map(Number).sort((a,b)=>a-b);
 if(JSON.stringify(keys)!=='[11,27,29,31]')throw Error('different six-dimensional rows');
 if(only&&only.some(k=>!keys.includes(k)))throw Error('unknown size');
 for(const k of only||keys){
  const[q,m,t,ex,raw]=data[k],C=JSON.parse(zlib.inflateSync(Buffer.from(raw,'base64'))),numbers=x=>Array.isArray(x)?x.flatMap(numbers):[x];
  if(q!==k||C.length!==8||C[0]!==6||C[1]!==q||!(C[2]>=0&&C[2]<=15&&C[3]>0&&C[4].length<=30&&C[5].length===C[2]+1&&t>0)||!numbers(C).every(Number.isSafeInteger))throw Error('invalid chart encoding');
  const[u,z]=direct(C,R(1,t));
  if(show(u)!==ex||-divfloor(-1000000n*u[0],u[1])!==BigInt(m))throw Error('different energy '+q);
  console.log('PASS source',q,ex,'Bernstein nodes',z.nodes);
 }
}
function solve(W,L0){
 const T=78,A=Array.from({length:77},()=>new Map());A[0].set(0,0);
 // Key = 78*odd component count + singleton count. Integers stay <2^53.
 const items=[1,...Array.from({length:36},(_,i)=>5+2*i)];
 for(let n=0;n<=76;n++)for(const[h,c] of A[n]){
  const o=Math.floor(h/T),s=h%T;for(const k of items)if(n+k<=76){
   const j=(o+1)*T+s+(k===1?1:0);
   A[n+k].set(j,Math.min(A[n+k].get(j)??Infinity,c+W[k]));
  }
 }
 const best=Array(77).fill(Infinity);
 for(let n=0;n<=76;n++)for(let t=0;t<=n;t++)for(const[h,c]of A[n-t]){
  const o=Math.floor(h/T),s=h%T;
  if(n-t+s<=76 && n-t+o>=2*L0)best[n]=Math.min(best[n],c);
 }
 return best;
}
function budget(data,ref){
 const hash=crypto.createHash('sha256').update(ref).digest('hex');
 if(hash!=='0a5e03c9b1c3e9549fd19eb8ccd4849af9883cf307e27fee1036bed9613e2ba3')throw Error('changed predecessor weights');
 const W=JSON.parse(ref).weights.slice();if(W.length!==133)throw Error('incomplete charges');
 for(const [q,m,t,ex]of Object.values(data)){
  const[a,b]=ex.split('/').map(BigInt);W[q]=Math.max(W[q],Number(BigInt(q)*1000000n*b/a));
 }
 const b40=solve(W,40),b41=solve(W,41),lo=Math.min(...b40.slice(0,75)),hi=Math.min(...b41);
 if(lo!==48001424||hi!==49593325||Math.min(...b40.slice(0,74))!==48178508)throw Error('unexpected component census '+[lo,hi]);
 console.log('PASS minimum charges: >=40 parts with N<=74:',lo,'; >=41 parts with N<=76:',hi);
}
if(require.main===module){
 const d=JSON.parse(read('kissing-six-forty-component-charts.json'));
 const sel=process.argv.slice(2);if(sel[0]!=='budget')verifyCharts(d,sel.length?sel.map(Number):null);
 if(!sel.length||sel[0]==='budget')budget(d,read('kissing-132-mixed-inputs.json'));
}
module.exports={verifyCharts,budget};
