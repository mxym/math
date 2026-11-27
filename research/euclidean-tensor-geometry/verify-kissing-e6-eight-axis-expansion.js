'use strict';
// All signed roots in this note have squared norm two.
const types=[];
for(let r=1;r<=6;r++){
 types.push({r,n:r*(r+1)/2,d:r+1,k:'A'+r});
 if(r>=4)types.push({r,n:r*(r-1),d:4,k:'D'+r});
 if(r===6)types.push({r,n:36,d:3,k:'E6'});
}
const residual=[];function go(i,rank,n,d,T){if(T.length&&n>=8&&n<=9&&!T.some(k=>k[0]!=='A'||+k.slice(1)>=4))residual.push([T.join('+'),rank,n,d]);
 for(let j=i;j<types.length;j++){const t=types[j];if(rank+t.r<=6)go(j,rank+t.r,n+t.n,d*t.d,T.concat([t.k]));}}go(0,0,0,1,[]);
const expected=['A1+A1+A1+A3','A1+A1+A2+A2','A1+A1+A3','A2+A2+A2','A2+A3'].sort();
if(JSON.stringify(residual.map(v=>v[0]).sort())!==JSON.stringify(expected))throw Error('ADE cases');
// Products for the 27+27 reference axes of two inequivalent A2^3 glue choices.
const list=[];for(let i=0;i<3;i++)for(let j=0;j<3;j++)for(let k=0;k<3;k++)list.push([i,j,k]);
const graph=Array.from({length:54},()=>[]);
for(const [a,x] of list.entries())for(const [b,y] of list.entries()){
 const p=3*(-(x[0]===y[0])+(x[1]===y[1])+(x[2]===y[2]))-1;
 if(Math.abs(p)>3){const s=p>0?-1:1;graph[a].push([27+b,s]);graph[27+b].push([a,s]);}}
const bits=new Int8Array(54);let bad=false;for(let i=0;i<54;i++)if(!bits[i]){bits[i]=1;const q=[i];
 for(let j=0;j<q.length;j++)for(const [k,s] of graph[q[j]])if(!bits[k]){bits[k]=bits[q[j]]*s;q.push(k);}else if(bits[k]!==bits[q[j]]*s)bad=true;}if(!bad)throw Error('A2^3 sign obstruction');
// Exact two-torsion quadratic classes in A3 + A1 + A1 (twice the norm modulo 4).
const gl=[];for(let u=0;u<2;u++)for(let v=0;v<2;v++)for(let w=0;w<2;w++)if((u||v||w)&&!( (2*u+v+w)%4))gl.push([u,v,w]);if(String(gl)!=='1,1,1')throw Error('glue');
// Verify the abstract counting inequalities in the centered case.
for(let m=0;m<=12;m++){function ck(K){const r=K.length,t=K.reduce((a,x)=>a+x,0),inc=4*r+t;
if(inc<=2*m&&inc-r*(r-1)/2<=m&&K.every(k=>4+k<=m)&&K.every((a,i)=>K.every((b,j)=>i===j||7+a+b<=m))&&
 K.every((a,i)=>K.every((b,j)=>K.every((c,k)=>new Set([i,j,k]).size<3||9+a+b+c<=m)))){
 if(K.reduce((a,k)=>a+(k===4?8:k+2),0)>m)throw Error('center count '+[m,...K]);}
 if(r<Math.floor(m/2))for(let k=K.at(-1)||0;k<=4;k++)ck(K.concat([k]));}ck([]);}
for(let e=0;e<=2;e++)if(6+3*e>10+e)throw Error('noncenter count');
console.log(residual,gl,'A2^3 inconsistent; centered and positive-orthant bounds pass');