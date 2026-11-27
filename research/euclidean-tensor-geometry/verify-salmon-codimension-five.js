#!/usr/bin/env node
'use strict';
function check(kind){

const n=4,p=101,mod=x=>(x%p+p)%p, ix=(i,j,k)=>(i*4+j)*4+k;
const prod=(a,b)=>a.map((r,i)=>r.map((_,j)=>r.reduce((s,e,k)=>s+e*b[k][j],0)));
const perm=n=>{const z=[];function f(a,b,s){if(!b.length){z.push([a,s]);return;}b.forEach((v,i)=>f(a.concat(v),b.filter((_,j)=>i!==j),s*(i%2?-1:1)))}f([],[...Array(n).keys()],1);return z};
const ps=perm(3);
function adj(A,B){let c=Array.from({length:4},()=>Array(4).fill(0)),d=c.map(r=>r.slice());
for(let i=0;i<4;i++)for(let j=0;j<4;j++){const ir=[0,1,2,3].filter(k=>k!==j),ic=[0,1,2,3].filter(k=>k!==i);for(const [z,s0] of ps){const s=(i+j)%2?-s0:s0;const u=ir.map((h,k)=>A[h][ic[z[k]]]);c[i][j]+=s*u[0]*u[1]*u[2];if(B){const v=ir.map((h,k)=>B[h][ic[z[k]]]);d[i][j]+=s*(v[0]*u[1]*u[2]+u[0]*v[1]*u[2]+u[0]*u[1]*v[2]);}}}return [c,d];}
const ranker=()=>{const rows=[],src=[],raw=[];return {rows,src,raw,add:(a,k)=>{const orig=a.slice();a=a.map(mod);for(const r of rows){let x=a[r.i];if(x)a=a.map((v,j)=>mod(v-x*r.a[j]));}const i=a.findIndex(x=>x!==0);if(i<0)return;let v=1;while(mod(v*a[i])!==1)v++;rows.push({a:a.map(x=>mod(x*v)),i});src.push(k);raw.push(orig);}}};
const T=Array(64).fill(0);

const I=[[1,0,0],[0,1,0],[0,0,1]],u=[1,1,1], frame=I.concat([u]);
const A=kind==="distinct"||kind==="flag2"?I.concat([[1,1,0]]):kind==="flag1"?I.concat([[1,0,1]]):frame;
const B=kind==="distinct"?I.concat([[1,0,1]]):frame;
const data = kind==="distinct"?[[0,0,0],[1,1,1],[2,2,2],[3,3,3]]:kind==="flag1"||kind==="flag2"?[[1,0,0],[0,1,0],[0,0,1],[2,2,2],[3,3,3]]:kind==="dual2"?[[1,0,0],[0,1,0],[0,0,1],[3,2,2],[2,3,2],[2,2,3]]:[[2,0,0],[1,1,0],[0,2,0],[1,0,1],[0,1,1],[0,0,2],[3,3,3]];
for(const [i,j,k] of data) for(let x=0;x<3;x++)for(let y=0;y<3;y++) T[ix(x,y,k)]+=A[i][x]*B[j][y];
const R=ranker(), save={P:[]};
const U=[0,1,2,3].map(i=>[0,1,2,3].map(j=>i===j?1:0));
const ords=[[0,1,2],[1,2,0],[2,0,1]];
function idx(order,i,j,k){const a=[];a[order[0]]=i;a[order[1]]=j;a[order[2]]=k;return ix(...a);}
function slice(a,order,v){return U.map((_,i)=>U.map((_,j)=>[0,1,2,3].reduce((s,k)=>s+a[idx(order,i,j,k)]*v[k],0)));}
function e_m(A,B,C,D,E,F){const ca=prod(A,prod(B,C)),cb=prod(D,prod(E,F));return ca.map((r,i)=>r.map((v,j)=>v-cb[i][j]));}
function add5(order,x,y,z){
const X=slice(T,order,x),Y=slice(T,order,y),Z=slice(T,order,z), A=adj(Y)[0];
const g=Array.from({length:16},()=>Array(64).fill(0));
for(let k=0;k<64;k++){const q=Array(64).fill(0);q[k]=1; const U1=slice(q,order,x),U2=adj(Y,slice(q,order,y))[1], U3=slice(q,order,z);
const G1=e_m(U1,A,Z,Z,A,U1),G2=e_m(X,U2,Z,Z,U2,X),G3=e_m(X,A,U3,U3,A,X);
for(let i=0;i<4;i++)for(let j=0;j<4;j++)g[4*i+j][k]=G1[i][j]+G2[i][j]+G3[i][j];}
g.forEach((r,i)=>R.add(r,{degree:5,order,x,y,z,i}));
}
const ys=U.concat([[1,1,1,1],[1,2,3,4],[3,-1,2,1],[1,3,0,2]]);
for(const ord of ords)for(let i=0;i<4;i++)for(let j=i+1;j<4;j++)for(const y of ys)add5(ord,U[i],y,U[j]);
if(typeof more!=="undefined")more({R, T, ix, perm, ords, idx});
return {rank:R.rows.length,src:R.src,pivots:R.rows.map(r=>r.i),raw:R.raw};


function more({R,T,ix,perm,ords,idx}){
const ps3=perm(3),ps4=perm(4),G=Array.from({length:6},(_,i)=>i);
let witness=[];
const columns=[[0,2,4],[1,3,5],[0,1,2],[3,4,5]];
const a=0,b=3;for(let k=0;k<4;k++)for(let l=k;l<4;l++){
 const G4=G.filter(i=>i!==a&&i!==b);
 const row=Array(64).fill(0);
 let value=0;
 for(const [aa,as] of ps3)for(const [ab,at] of ps3)for(const [ba,bs] of ps3)for(const [bb,bt] of ps3)for(const [cc,cs] of ps4){
 const A=[],B=[],C=[];C[a]=k;C[b]=l;
 for(let u=0;u<3;u++){A[columns[0][u]]=aa[u];A[columns[1][u]]=ab[u];B[columns[2][u]]=ba[u];B[columns[3][u]]=bb[u];}
 for(let u=0;u<4;u++)C[G4[u]]=cc[u];
 const loc=G.map(i=>ix(A[i],B[i],C[i])),z=G.filter(i=>T[loc[i]]===0),sg=as*at*bs*bt*cs;
 // Use the actual tensor coefficients, including the entry 2 in the two-dual sample.
 if(z.length<=1){
   const prod=loc.reduce((acc,j)=>acc*(T[j]||1),sg);
   if(!z.length){value+=prod;for(const j of loc)row[j]+=prod/T[j];}
   else row[loc[z[0]]]+=prod;
 }
 }
 if(value!==0)throw Error("not zero");
 R.add(row,{degree:6,a,b,k,l});
 if(R.rows.length===24)return
}
}
}
function det(a,p){const m=x=>(x%p+p)%p;a=a.map(r=>r.map(m));let c=1;for(let i=0;i<a.length;i++){let j=i;while(j<a.length&&!a[j][i])j++;if(j===a.length)return 0;if(j!==i){[a[i],a[j]]=[a[j],a[i]];c=p-c;}const x=a[i][i];c=c*x%p;let inv=1;while(x*inv%p!==1)inv++;for(j=i+1;j<a.length;j++){const q=a[j][i]*inv%p;for(let k=i;k<a.length;k++)a[j][k]=m(a[j][k]-q*a[i][k]);}}return c}
const expected={distinct:41,flag1:28,flag2:41,dual2:12,triple:33};
for(const [kind,e] of Object.entries(expected)){
  const r=check(kind),minor=det(r.raw.map(row=>r.pivots.map(c=>row[c])),101);
  if(r.rank!==24||minor!==e||r.src.filter(x=>x.degree===5).length!==20)
    throw Error(JSON.stringify({kind,rank:r.rank,minor}));
  console.log(JSON.stringify({kind,rank:r.rank,minor,pivots:r.pivots,rows:r.src}));
}
