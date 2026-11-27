#!/usr/bin/env node
'use strict';
const r=(()=>{

const n=4,p=101,mod=x=>(x%p+p)%p, ix=(i,j,k)=>(i*4+j)*4+k;
const prod=(a,b)=>a.map((r,i)=>r.map((_,j)=>r.reduce((s,e,k)=>s+e*b[k][j],0)));
const perm=n=>{const z=[];function f(a,b,s){if(!b.length){z.push([a,s]);return;}b.forEach((v,i)=>f(a.concat(v),b.filter((_,j)=>i!==j),s*(i%2?-1:1)))}f([],[...Array(n).keys()],1);return z};
const ps=perm(3);
function adj(A,B){let c=Array.from({length:4},()=>Array(4).fill(0)),d=c.map(r=>r.slice());
for(let i=0;i<4;i++)for(let j=0;j<4;j++){const ir=[0,1,2,3].filter(k=>k!==j),ic=[0,1,2,3].filter(k=>k!==i);for(const [z,s0] of ps){const s=(i+j)%2?-s0:s0;const u=ir.map((h,k)=>A[h][ic[z[k]]]);c[i][j]+=s*u[0]*u[1]*u[2];if(B){const v=ir.map((h,k)=>B[h][ic[z[k]]]);d[i][j]+=s*(v[0]*u[1]*u[2]+u[0]*v[1]*u[2]+u[0]*u[1]*v[2]);}}}return [c,d];}
const ranker=()=>{const rows=[],src=[],raw=[];return {rows,src,raw,add:(a,k)=>{const orig=a.slice();a=a.map(mod);for(const r of rows){let x=a[r.i];if(x)a=a.map((v,j)=>mod(v-x*r.a[j]));}const i=a.findIndex(x=>x!==0);if(i<0)return;let v=1;while(mod(v*a[i])!==1)v++;rows.push({a:a.map(x=>mod(x*v)),i});src.push(k);raw.push(orig);}}};
const T=Array(64).fill(0);for(let i=0;i<3;i++) T[ix(i,i,i)]=1;for(let i=0;i<3;i++)for(let j=0;j<3;j++)for(let k=0;k<3;k++)T[ix(i,j,k)]+=1;
const R=ranker(), save={P:[]};
const U=[0,1,2,3].map(i=>[0,1,2,3].map(j=>i===j?1:0));
const ords=[[0,1,2],[1,2,0],[2,0,1]];
function idx(order,i,j,k){const a=[];a[order[0]]=i;a[order[1]]=j;a[order[2]]=k;return ix(...a);}
function slice(a,order,v){return U.map((_,i)=>U.map((_,j)=>[0,1,2,3].reduce((s,k)=>s+a[idx(order,i,j,k)]*v[k],0)));}
function e_m(A,B,C,D,E,F){const ca=prod(A,prod(B,C)),cb=prod(D,prod(E,F));return ca.map((r,i)=>r.map((v,j)=>v-cb[i][j]));}

const qDirs=[];
for(let f=0;f<3;f++)for(let i=0;i<3;i++)for(let j=i+1;j<3;j++){const a=Array(64).fill(0);let s=[],t=[],k=0;
 for(let h=0;h<3;h++)if(h===f)s[h]=t[h]=3;else {s[h]=k++===0?i:j;t[h]=s[h]===i?j:i;}
 a[ix(...s)]=a[ix(...t)]=1;qDirs.push(a);
}
const all=qDirs.slice();for(let i=0;i<9;i++)for(let j=i+1;j<9;j++)all.push(qDirs[i].map((x,k)=>x+qDirs[j][k]));
function adj2(A,B){const d=Array.from({length:4},()=>Array(4).fill(0));
for(let i=0;i<4;i++)for(let j=0;j<4;j++){const ir=[0,1,2,3].filter(k=>k!==j),ic=[0,1,2,3].filter(k=>k!==i);for(const [z,s0] of ps){const s=(i+j)%2?-s0:s0;const u=ir.map((h,k)=>A[h][ic[z[k]]]),v=ir.map((h,k)=>B[h][ic[z[k]]]);d[i][j]+=s*(u[0]*v[1]*v[2]+v[0]*u[1]*v[2]+v[0]*v[1]*u[2]);}}return d;}

function add5(order,x,y,z){
const X=slice(T,order,x),Y=slice(T,order,y),Z=slice(T,order,z), A=adj(Y)[0];
const g=Array.from({length:16},()=>Array(64).fill(0));
for(let k=0;k<64;k++){const q=Array(64).fill(0);q[k]=1; const U1=slice(q,order,x),U2=adj(Y,slice(q,order,y))[1], U3=slice(q,order,z);
const G1=e_m(U1,A,Z,Z,A,U1),G2=e_m(X,U2,Z,Z,U2,X),G3=e_m(X,A,U3,U3,A,X);
for(let i=0;i<4;i++)for(let j=0;j<4;j++)g[4*i+j][k]=G1[i][j]+G2[i][j]+G3[i][j];}

for(const q of all){const U1=slice(q,order,x),V1=slice(q,order,z),dY=slice(q,order,y),U2=adj(Y,dY)[1],V2=adj2(Y,dY);
const H1=e_m(U1,U2,Z,Z,U2,U1), H2=e_m(U1,A,V1,V1,A,U1), H3=e_m(X,V2,Z,Z,V2,X), H4=e_m(X,U2,V1,V1,U2,X);
for(let i=0;i<4;i++)for(let j=0;j<4;j++)g[4*i+j].push(H1[i][j]+H2[i][j]+H3[i][j]+H4[i][j]);
}
g.forEach((r,i)=>R.add(r,{degree:5,order,x,y,z,i}));

}
const ys=U.concat([[1,1,1,1],[1,2,3,4],[3,-1,2,1],[1,3,0,2]]);
for(const ord of ords)for(let i=0;i<4;i++)for(let j=i+1;j<4;j++)for(const y of ys)add5(ord,U[i],y,U[j]);

return {rank:R.rows.length,src:R.src,pivots:R.rows.map(r=>r.i),raw:R.raw};



})();
const count = r.pivots.filter(x=>x>=64).length;
if(r.rank!==19||count!==9) throw Error(JSON.stringify({r:r.rank,quad:count}));
function data(y,i){
  const h=r.src.findIndex(x=>x.order.join()==='0,1,2'&&x.x.join()==='1,0,0,0'&&
    x.z.join()==='0,1,0,0'&&x.y.join()===y&&x.i===i);
  if(h<0)throw Error('specified row not retained');
  return r.raw[h];
}
const f=data('0,0,1,0',0),g=data('1,1,1,1',0);
const a=data('0,0,1,0',1),b=data('0,0,1,0',4),h=a.map((x,i)=>x+b[i]);
const d=(x,i,j)=>x[i]*x[3+j]-x[j]*x[3+i];
const p=[x=>-d(x,0,1)+d(x,0,2)-d(x,1,2),
         x=>-6*d(x,0,1)+2*d(x,0,2)-2*d(x,1,2),x=>-4*d(x,1,2)];
const e=Array.from({length:9},(_,i)=>Array.from({length:9},(_,j)=>i===j?1:0));
const dirs=e.slice();for(let i=0;i<9;i++)for(let j=i+1;j<9;j++)dirs.push(e[i].map((x,k)=>x+e[j][k]));
for(const [i,row] of [f,g,h].entries()){
  if(row.slice(0,64).some(Boolean))throw Error('gradient not zero');
  if(row.slice(64).some((x,j)=>x!==p[i](dirs[j])))throw Error('quadratic identity mismatch');
}
console.log(JSON.stringify({linearRank:10,pureQuadraticRank:9,determinantOfCoefficients:-16}));
