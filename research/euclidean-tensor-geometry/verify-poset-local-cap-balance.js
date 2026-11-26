'use strict';
const check=(v,m)=>{if(!v)throw Error(m);};
// A state in the lattice of chain prefixes determines every available next vertex.
function count(n,E){
 const dims=n.map(x=>x+1),pre=n.map(x=>Array.from({length:x+1},()=>[0,0,0]));
 for(const [a,i,b,j] of E)pre[b][j][a]=Math.max(pre[b][j][a],i);
 const sz=dims.reduce((a,b)=>a*b,1),P=Array(sz).fill(0n);
 const at=([i,j,k])=>(i*dims[1]+j)*dims[2]+k;
 P[0]=1n;
 for(let i=0;i<=n[0];i++)for(let j=0;j<=n[1];j++)for(let k=0;k<=n[2];k++){
  const a=[i,j,k],t=P[at(a)];if(!t)continue;
  for(let q=0;q<3;q++)if(a[q]<n[q]&&pre[q][a[q]+1].every((x,h)=>x<=a[h])){
   const b=a.slice();b[q]++;P[at(b)]+=t;
  }
 }
 return P.at(-1);
}
function reach(n,edges,start,reverse){
 const E=edges.slice();
 for(let q=0;q<3;q++)for(let j=1;j<n[q];j++)E.push([q,j,q,j+1]);
 let S=new Set([start.join(':')]);
 for(let repeat=true;repeat;){
  repeat=false;
  for(const r of E){
   const a=r.slice(0,2).join(':'),b=r.slice(2).join(':');
   if((reverse?S.has(b)&&!S.has(a):S.has(a)&&!S.has(b))){
    S.add(reverse?a:b);repeat=true;
   }
  }
 }
 return S.size;
}
function run(n,k,E,q,want,knownOne){
 const total=count(n,E),good=count(n,[...E,q]);
 const m=n.map((x,i)=>x-2*k[i]);
 const l=[0,1].map(a=>reach(n,E,[a,k[a]],true));
 const u=[0,1].map(a=>reach(n,E,[a,n[a]-k[a]+1],false));
 check(l[0]*u[1]<m[0]*m[1]&&l[1]*u[0]<m[0]*m[1],'local caps');
 check(3n*good>=total&&3n*good<=2n*total,'not balanced');
 const decimal=(10n**10n*good*2n+total)/(2n*total);
 if(knownOne)check(decimal===want,'unexpected fraction');
 return {n,k,early:l,late:u,m,good:''+good,total:''+total,probability:'0.'+decimal};
}
const z=(n,k)=>n-k+1;
const cases=[
 run([36,36,36],[10,10,10],[[0,10,1,1],[1,36,2,27],[2,2,0,27]],[0,20,1,16],5030981569n,true),
 run([42,42,42],[8,8,8],[[0,8,1,1],[1,8,2,1],[2,42,1,z(42,8)],[1,42,0,z(42,8)],[0,2,2,39]],[0,17,1,16],5081453129n,true),
 run([16,36,26],[2,4,3],[[0,2,1,1],[1,36,2,24],[2,2,0,15]],[0,8,1,16],5386047081n,true),
];
for(const x of cases)(typeof console==='undefined'?text:console.log)(x);
