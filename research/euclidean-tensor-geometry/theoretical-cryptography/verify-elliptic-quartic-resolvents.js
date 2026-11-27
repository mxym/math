'use strict';
// Checks the finite permutation-group comparisons and the tiny base-parameter examples.
const id=[0,1,2,3];
const mul=(a,b)=>b.map(i=>a[i]);
const key=p=>p.join('');
const perm=a=>a.length===0?[[]]:a.flatMap((v,i)=>perm(a.filter((_,j)=>i!==j)).map(x=>[v,...x]));
const P=perm(id);
const ind=new Map(P.map((p,i)=>[key(p),i]));
const e=ind.get(key(id)), pg=P.map(a=>P.map(b=>ind.get(key(mul(a,b)))));
const inverse=P.map((_,i)=>pg[i].indexOf(e));
function orbits(H,n,action){
 const seen=new Set();let count=0;
 for(let i=0;i<n;i++)if(!seen.has(i)){
  count++;for(const h of H)seen.add(action(h,i));
 }
 return count;
}
const part=[[1,0,3,2],[2,3,0,1],[3,2,1,0]];
const act=(h,i)=>part.findIndex(p=>key(p)===key(mul(mul(P[h],part[i]),P[inverse[h]])));
const parity=P.map(a=>a.reduce((s,v,i)=>s+a.slice(i+1).filter(t=>t<v).length,0)%2);
function generated(g){
 const H=new Set([e]),list=[e];
 for(let i=0;i<list.length;i++)for(const j of g){
  const k=pg[list[i]][j];if(!H.has(k)){H.add(k);list.push(k)}
 }
 return list.sort((a,b)=>a-b);
}
const all=[[e]],seen=new Set([String([e])]);
for(let i=0;i<all.length;i++)for(let j=0;j<P.length;j++){
 if(all[i].includes(j))continue;
 const H=generated([...all[i],j]), k=String(H);
 if(!seen.has(k)){seen.add(k);all.push(H)}
}
const assert=(p,msg)=>{if(!p)throw Error(msg)};
assert(all.length===30,'S4 subgroup count');
for(const H of all){
 const d4=4-orbits(H,4,(h,i)=>P[h][i]),d3=3-orbits(H,3,act);
 const d2=2-orbits(H,2,(h,i)=>(i+parity[h])%2);
 assert(d3<=d4&&d2<=d4,'resolvent different');
 assert(2*(H.length-1)<=H.length*d4,'S4 genus coefficient');
 if(H.every(i=>!parity[i]))assert(3*(H.length-1)<=H.length*d4,'A4 genus coefficient');
}
let cycleCount=0;
for(let p=0;p<P.length;p++){
 const type31=pg[pg[p][p]][p]===e&&p!==e;
 const nC=[0,1,2].filter(i=>act(p,i)===i).length,nD=parity[p]?0:2;
 assert(1-nC+nD===3*Number(type31),'resolvent indicator');
 if(type31)cycleCount++;
}
assert(cycleCount===8,'three cycles');
const cubes7=new Set(Array.from({length:7},(_,i)=>i**3%7));
const eligible7=[2,3,4,5].filter(x=>!cubes7.has(x));
assert(eligible7.join(',')==='2,3,4,5','regular A4 toy fibers');
assert(P.filter((_,p)=>parity[p]&&p!==e&&pg[pg[p][p]][p]===e).length===0,'odd Frobenius coset');
console.log({subgroups:all.length,cycleCount,regularA4F7:eligible7,oddCosetFibers:0});
