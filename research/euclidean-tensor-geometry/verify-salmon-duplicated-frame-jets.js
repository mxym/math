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

for(const [i,j,k] of [[0,0,0],[0,1,1],[1,2,2]])T[ix(i,j,k)]=1;for(let j=0;j<3;j++)T[ix(2,j,3)]=1;
const R=ranker();
const U=[0,1,2,3].map(i=>[0,1,2,3].map(j=>i===j?1:0));
const ords=[[0,1,2],[1,2,0],[2,0,1]];
function idx(order,i,j,k){const a=[];a[order[0]]=i;a[order[1]]=j;a[order[2]]=k;return ix(...a);}
function slice(a,order,v){return U.map((_,i)=>U.map((_,j)=>[0,1,2,3].reduce((s,k)=>s+a[idx(order,i,j,k)]*v[k],0)));}
function e_m(A,B,C,D,E,F){const ca=prod(A,prod(B,C)),cb=prod(D,prod(E,F));return ca.map((r,i)=>r.map((v,j)=>v-cb[i][j]));}

const normals=[1,2,3].flatMap(i=>[[0,1],[1,0],[1,1]].map(([j,k])=>ix(i,j,k)));
const pairs=Array.from({length:9},(_,i)=>Array.from({length:8-i},(_,j)=>[i,i+j+1])).flat();
const inputs=normals.map(x=>[x]).concat(pairs.map(([a,b])=>[normals[a],normals[b]]));
const Q=ranker();
const add=(a,b,s=1)=>a.map((v,i)=>mod(v+s*b[i]));
const m=(a,b)=>[mod(a[0]*b[0]),mod(a[0]*b[1]+a[1]*b[0]),mod(a[0]*b[2]+a[1]*b[1]+a[2]*b[0])];
const zero=()=>[0,0,0];
function de(A){if(A.length===1)return A[0][0];let v=zero();
 for(let j=0;j<A.length;j++)v=add(v,m(A[0][j],de(A.slice(1).map(r=>r.filter((_,k)=>k!==j)))),j%2?-1:1);
 return v;
}
const ad=A=>A.map((r,i)=>r.map((v,j)=>de(A.filter((_,k)=>k!==j).map(s=>s.filter((_,k)=>k!==i))).map(u=>mod(((i+j)%2?-1:1)*u))));
const mm=(a,b)=>a.map((r,i)=>r.map((_,j)=>r.reduce((s,v,k)=>add(s,m(v,b[k][j])),zero())));
function jet(order,x,y,z,inputs){
 const s=w=>U.map((_,i)=>U.map((_,j)=>Array.from({length:4},(_,k)=>idx(order,i,j,k)).reduce((v,l,k)=>add(v,[T[l],+inputs.includes(l),0],w[k]),zero())));
 const A=s(x),B=ad(s(y)),C=s(z),L=mm(mm(A,B),C),M=mm(mm(C,B),A);
 return L.flatMap((r,i)=>r.map((p,j)=>mod(p[2]-M[i][j][2])));
}
function add5(order,x,y,z){
const X=slice(T,order,x),Y=slice(T,order,y),Z=slice(T,order,z), A=adj(Y)[0];
const g=Array.from({length:16},()=>Array(64).fill(0));
for(let k=0;k<64;k++){const q=Array(64).fill(0);q[k]=1; const U1=slice(q,order,x),U2=adj(Y,slice(q,order,y))[1], U3=slice(q,order,z);
const G1=e_m(U1,A,Z,Z,A,U1),G2=e_m(X,U2,Z,Z,U2,X),G3=e_m(X,A,U3,U3,A,X);
for(let i=0;i<4;i++)for(let j=0;j<4;j++)g[4*i+j][k]=G1[i][j]+G2[i][j]+G3[i][j];}

const h=inputs.map(P=>jet(order,x,y,z,P));
g.forEach((r,i)=>{
 R.add(r,{degree:5,order,x,y,z,i});
 const f=h.slice(0,9).map(a=>a[i]);
 Q.add(r.concat(f,pairs.map(([j,k],t)=>mod(h[t+9][i]-f[j]-f[k]))),{degree:5,order,x,y,z,i});
});
}
const ys=U.concat([[1,1,1,1],[1,2,3,4],[3,-1,2,1],[1,3,0,2]]);
for(const ord of ords)for(let i=0;i<4;i++)for(let j=i+1;j<4;j++)for(const y of ys)add5(ord,U[i],y,U[j]);
console.log({quinticLin:R.rows.length,quinticLinQ:Q.rows.length,quadratic:Q.rows.length-R.rows.length}); more({R,Q,T,ix,perm,ords,idx,normals,pairs});console.log({totalLin:R.rows.length,totalLinQ:Q.rows.length,quadratic:Q.rows.length-R.rows.length});
return {rank:R.rows.length,src:R.src,pivots:R.rows.map(r=>r.i),raw:R.raw,augRank:Q.rows.length,augPivots:Q.rows.map(q=>q.i),augRaw:Q.raw};


function more({R,Q,T,ix,perm,ords,idx,normals,pairs}){
 const ps3=perm(3),ps4=perm(4),G=[0,1,2,3,4,5],cols=[[0,2,4],[1,3,5],[0,1,2],[3,4,5]];
 const tri=[0,1,2,3].map(r=>[0,1,2,3].filter(q=>q!==r));
 function sext(order,A0,A1,B0,B1,k,l){
 const row=Array(109).fill(0), Ni=new Map(normals.map((x,i)=>[x,i])), qi=(u,v)=>u===v?u:9+pairs.findIndex(([i,j])=>i===Math.min(u,v)&&j===Math.max(u,v));
 for(const [aa,as] of ps3)for(const [ab,at] of ps3)for(const [ba,bs] of ps3)for(const [bb,bt] of ps3)for(const [cc,cs] of ps4){
 const A=[],B=[],C=[k,cc[0],cc[1],l,cc[2],cc[3]];
 for(let u=0;u<3;u++){A[cols[0][u]]=A0[aa[u]];A[cols[1][u]]=A1[ab[u]];B[cols[2][u]]=B0[ba[u]];B[cols[3][u]]=B1[bb[u]];}
 const L=G.map(i=>idx(order,A[i],B[i],C[i]));const check=L.filter(i=>T[i]===0),sign=as*at*bs*bt*cs;
 if(check.length===2&&check.every(i=>Ni.has(i)))row[64+qi(Ni.get(check[0]),Ni.get(check[1]))]+=sign*L.reduce((v,i)=>v*(T[i]||1),1);
 if(check.length===1)row[check[0]]+=sign*L.reduce((v,i)=>v*(T[i]||1),1);
 else if(!check.length)for(const i of L)row[i]+=sign*L.reduce((v,j)=>v*T[j],1)/T[i];
 }return row;
 }
 const core=tri[3];function push(v,key){R.add(v.slice(0,64),key);Q.add(v,key);}
 for(const O of ords){
 const [A,B,C]=O;
 if(C===2){
 for(let k=0;k<4;k++)for(let l=k;l<4;l++) {
 push(sext(O,core,core,core,core,k,l),{degree:6,O,k,l});
 for(const V of tri.slice(0,3))for(let q=0;q<2;q++){
 const r= q===0?sext(O,V,core,core,core,k,l):sext(O,core,core,V,core,k,l);
 const t= q===0?sext(O,core,V,core,core,k,l):sext(O,core,core,core,V,k,l);
 push(r.map((v,i)=>v+t[i]),{degree:6,O,k,l});
 }
 if(Q.rows.length===29)return;
 }
 }else{
 for(let k=0;k<3;k++)for(let l=k;l<3;l++)for(const V of tri) {
 const a=A===2?V:core,b=B===2?V:core;
 push(sext(O,a,a,b,b,k,l),{degree:6,O,k,l});
 if(Q.rows.length===29)return;
 }
 }
 }
}
}
function det(a,p){const m=x=>(x%p+p)%p;a=a.map(r=>r.map(m));let c=1;for(let i=0;i<a.length;i++){let j=i;while(j<a.length&&!a[j][i])j++;if(j===a.length)return 0;if(j!==i){[a[i],a[j]]=[a[j],a[i]];c=p-c;}const x=a[i][i];c=c*x%p;let inv=1;while(x*inv%p!==1)inv++;for(j=i+1;j<a.length;j++){const q=a[j][i]*inv%p;for(let k=i;k<a.length;k++)a[j][k]=m(a[j][k]-q*a[i][k]);}}return c}
const r=check();
const lm=det(r.raw.map(row=>r.pivots.map(i=>row[i])),101);
const am=det(r.augRaw.map(row=>r.augPivots.map(i=>row[i])),101);
if(r.rank!==20||lm!==94||r.augRank!==29||am!==29)throw Error("wrong exact certificate");
console.log({linear:r.rank,linearMinor:lm,augmented:r.augRank,augMinor:am});
