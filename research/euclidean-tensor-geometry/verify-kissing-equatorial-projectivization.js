'use strict';
const assert=(x,m)=>{if(!x)throw Error(m);};
const vec=(n,f)=>Array.from({length:n},(_,i)=>f(i)),sum=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0),pc=x=>x?1+pc(x&(x-1)):0;
function check(points,gram,unit,cnt,paired){assert(points.length===cnt,'size');const P=new Set(points.map(p=>p.join()));assert(P.size===cnt,'distinct');const n=points.filter(p=>P.has(p.map(x=>-x).join())).length;assert(n===paired,'antipodes '+n);
 points.forEach((x,i)=>{assert(gram(x,x)===2*unit,'norm');for(let j=0;j<i;j++)assert(gram(x,points[j])<=unit,'product');});return {cnt,paired};}
function A(n){const roots=[];for(let i=0;i<n;i++)for(let j=0;j<n;j++)if(i!==j)roots.push(vec(n,k=>Number(k===i)-Number(k===j)));return roots;}
function D(n){const roots=[];for(let i=0;i<n;i++)for(let j=0;j<i;j++)for(const a of [-1,1])for(const b of [-1,1])roots.push(vec(n,k=>k===i?a:k===j?b:0));return roots;}
const T=vec(32,k=>k).filter(k=>pc(k)===2),seen=new Set([T[0]]);for(const a of seen)for(const b of T)if(!(a&b))seen.add(b);assert(seen.size===10,'Petersen connected');
for(const parity of [-1,1]){
 // Use five horizontal coordinates scaled by 5 and height in units 1/sqrt(5).
 const p=A(5).map(v=>v.map(x=>5*x).concat([0]));for(const h of [-2,2])for(const k of T){const s=h===2?1:parity;p.push(vec(5,j=>s*(5*(k>>j&1)-2)).concat([h]));}
 console.log('A4',check(p,(a,b)=>sum(a.slice(0,5),b)+5*a[5]*b[5],25,40,parity===-1?40:20));
}
const A5=A(6).map(v=>v.map(x=>2*x).concat([0]));for(const h of [-1,1]){A5.push([0,0,0,0,0,0,2*h]);for(let k=0;k<64;k++)if(pc(k)===3)A5.push(vec(6,j=>2*(k>>j&1)-1).concat([h]));}const gram=(a,b)=>sum(a.slice(0,6),b)+2*a[6]*b[6];console.log('A5',check(A5,gram,4,72,72));
for(const diff of [0,1]){const p=D(6).map(v=>v.map(x=>2*x).concat([0]));for(const h of [-1,1]){p.push([0,0,0,0,0,0,2*h]);for(let k=0;k<64;k++)if(pc(k)%2===(h===1?0:diff))p.push(vec(6,j=>2*(k>>j&1)-1).concat([h]));}console.log('D6',check(p,gram,4,126,diff?62:126));}
