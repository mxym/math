#!/usr/bin/env node
// Exact verification of new dimension-seven odd uniform-energy inputs. No external packages.
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
 return [T,Y,energy,H11,H111,hp];
}
function choose(n,k){if(k<0||k>n)return 0n;let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-i+1)/BigInt(i);return x;}
function divfloor(x,d){let z=x/d;return x<0n&&x%d?z-1n:z;}
function bern(A,dim,up=false){
 const ds=Array(dim).fill(0);for(const i of A.keys())idx(i).slice(0,dim).forEach((v,j)=>ds[j]=Math.max(ds[j],v));const stride=ds.map((_,j)=>ds.slice(0,j).reduce((s,n)=>s*(n+1),1)),L=ds.reduce((s,n)=>s*(n+1),1),v=Array(L).fill(Z);
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
 function go(U,Q,lo,hi,d){nodes++;if(nodes>9000000||d>75)throw Error('unresolved Bernstein box');if(U.A.every(x=>x>=0)){close++;return;}if(Q&&(Q.A.every(x=>x<0)||lo.some((v,i)=>i<dim-1&&v>hi[i+1]))){out++;return;}
  const k=d%dim,[l,r]=split(U,k,false),[p,q]=Q?split(Q,k,true):[null,null],mid=(lo[k]+hi[k])/2,h=hi.slice(),a=lo.slice();h[k]=mid;a[k]=mid;go(l,p,lo,h,d+1);go(r,q,a,hi,d+1);}
 go(V,G,Array(dim).fill(0),Array(dim).fill(1),0);return {nodes,close,out};
}
const determinant=sum(P(),scale(prod(prod(a,b),c),R(2)),scale(sum(prod(a,a),prod(b,b),prod(c,c)),R(-1)));


function direct(C,sl){
 const [T,Y,U]=build(C,Z,Z),q=C[1],V=plus(scale(T,R(3*(q-2))),P(0,mul(R(3),sl)));for(const[i,v]of Y){for(const k of[i,32*i,1024*i])put(V,k,v);}
 const c=check(bern(V,3),bern(determinant,3,true));return [add(U,mul(R(q-1),sl)),c];
}

const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const read=n=>fs.readFileSync(path.join(__dirname,n),'utf8');
const base=read('kissing-component-harmonic-data.json');
if(crypto.createHash('sha256').update(base).digest('hex')!=='309bd1cc2109cd5d5f97c84705ed4b05ec26e18c1be9cc1eec836e0e15f9cf8f')throw Error('different predecessor vector');
const w=JSON.parse(base).weights.slice(), goal=JSON.parse(read('kissing-131-component-data.json')),data=JSON.parse(read('kissing-131-uniform-data.json'));
const unit=1000000,oneB=1000000000,src=new Map(),ceil6=x=>-divfloor(-1000000n*x[0],x[1]);
function update(q,m){for(let k=q;k<=132;k+=2)w[k]=Math.max(w[k],Number(1000000000000n*BigInt(k*(q-1))/BigInt(750000*(q-1)+(k-1)*(m-750000))));}
for(const [row,isSource]of [...data.new.map(v=>[v,false]),...data.source.map(v=>[v,true])]){
 const[q,m,t,ex,raw]=row,C=JSON.parse(zlib.inflateSync(Buffer.from(raw,'base64')));
 if(C.length!==8||C[0]!==7||C[1]!==q||C[2]>10||C[4].length>24)throw Error('wrong chart identity');
 const[u,tree]=direct(C,R(1,t));if(show(u)!==ex||ceil6(u)!==BigInt(m))throw Error('wrong chart '+q);
 if(isSource){const[,,,J,H,h]=build(C,Z,Z);src.set(q,{J,H,h,B:add(R(C[6],C[3]),R(1,t))});}else update(q,m);
 console.log('PASS '+(isSource?'source':'new')+' chart',q,ex,tree.nodes);
}
function powQ(x,n){let v=O;for(let i=0;i<n;i++)v=mul(v,x);return v;}
function positive1(f){
 // Exact power-to-Bernstein conversion on [-1,1/2], then exact half splits.
 let d=Math.max(0,...f.keys()),A=Array(d+1).fill(Z),lo=R(-1),b=R(3,2);
 for(let j=0;j<=d;j++)for(const[k,c]of f)if(k>=j)A[j]=add(A[j],mul(c,mul(R(choose(k,j)),mul(powQ(b,j),powQ(lo,k-j)))));
 const B=A.map((_,i)=>A.slice(0,i+1).reduce((s,x,j)=>add(s,mul(x,R(choose(i,j),choose(d,j)))),Z));
 let M=0;
 function rec(z,dep){
  if(++M>300000||dep>70||z[0][0]<0n||z.at(-1)[0]<0n)throw Error('unproved transferred scalar bound');
  if(z.every(x=>x[0]>=0n))return;
  let t=z,l=[t[0]],r=[t.at(-1)];
  while(t.length>1){t=t.slice(1).map((x,j)=>mul(add(x,t[j]),R(1,2)));l.push(t[0]);r.push(t.at(-1));}rec(l,dep+1);rec(r.reverse(),dep+1);
 }rec(B,0);return M;
}
for(const[k,m,b0,u,rows]of data.transfer){
 if(rows.reduce((s,r)=>s+r[1],0)!==oneB||rows.some(r=>r[1]<0)||u.some(t=>t<0))throw Error('not a convex/positive transfer');
 const B=R(b0,oneB);let offset=P(0,B),mass=R(3,4);const cc=[P(),a];
 for(let j=1;j<u.length;j++)cc.push(scale(diff(scale(prod(a,cc[j]),R(2*j+5)),scale(cc[j-1],R(j))),R(1,j+5)));
 let h=lin(u.map(v=>R(v,oneB)),cc.slice(1));offset=diff(offset,h);
 for(const[q,num]of rows){const v=src.get(q);if(!v)throw Error('missing source');
  const x=R(num,oneB),e=R(q-2,k-2);offset=plus(offset,scale(sum(scale(v.J,mul(R(3),add(O,neg(e)))),v.h,P(0,neg(v.B))),x));
  mass=add(mass,mul(x,mul(e,v.H)));}
 mass=add(mass,add(R(u.reduce((s,x)=>s+BigInt(x),0n),oneB),mul(R(k-1),B)));
 const nodes=positive1(offset);if(ceil6(mass)!==BigInt(m))throw Error('different transferred bound');
 update(k,m);console.log('PASS transfer',k,m,nodes);
}
if(JSON.stringify(w)!==JSON.stringify(goal.weights))throw Error('different final reciprocal charge vector');
console.log('PASS all 133 charges');