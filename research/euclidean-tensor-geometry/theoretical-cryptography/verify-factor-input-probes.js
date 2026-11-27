"use strict";
// Only generated small promise sets and exact finite counts.
const assert=(x,m)=>{if(!x)throw Error(m);};
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
const pop=x=>{let k=0;while(x){x&=x-1;k++;}return k;};
const choose=(n,k)=>{let r=1;if(k>n)return 0;for(let j=0;j<k;j++)r=r*(n-j)/(j+1);return Math.round(r);};
const cap=(m,t)=>Array.from({length:t+1},(_,i)=>choose(m,i)).reduce((s,x)=>s+x,0);
const maskTable=new Map();
function masks(m){if(!maskTable.has(m))maskTable.set(m,Array.from({length:2**m},(_,i)=>[i,pop(i)]));return maskTable.get(m);}
let localPairs=0,blockChecks=0,fibers=0,abstractCubes=0,capacityChecks=0,replayChecks=0;
function listTests(U,m,withReplay){
 if(!U.length)return;
 const best=U.map(()=>Array(m+1).fill(U.length));
 for(const [mask,t] of masks(m)){
  const hist=new Map();
  for(const x of U){const s=x&mask;hist.set(s,(hist.get(s)||0)+1);}
  for(let i=0;i<U.length;i++)best[i][t]=Math.min(best[i][t],hist.get(U[i]&mask));
 }
 for(const R of best)for(let t=1;t<=m;t++)R[t]=Math.min(R[t],R[t-1]);
 for(let t=0;t<=m;t++)for(const K of [1,2,3,5]){
  const bad=best.filter(R=>R[t]<=K).length;
  assert(bad<=K*cap(m,t),"small-list degree/rank bound");capacityChecks++;
 }
 if(!withReplay||U.length<=1)return;
 for(let i=0;i<U.length;i++){
  const x=U[i],weights=Array.from({length:12},(_,j)=>[
   ((x+3)*(11+19*j)^(7*j*j+73*i))&(2**m-1),1+(j*j+i)%11
  ]);
  const betaNumer=Math.max(...U.filter(y=>y!==x).map(y=>
   weights.reduce((s,[mask,w])=>s+(((x^y)&mask)?0:w),0)));
  for(let t=0;t<=m;t++)for(const K of [1,2,3]){
   if(best[i][t]<=K)continue;
   const W=weights.filter(([mask])=>pop(mask)<=t).reduce((s,[,w])=>s+w,0);
   assert(K*W<=(U.length-1)*betaNumer,"weighted replay union");
   replayChecks++;
  }
 }
}
for(let m=1;m<=3;m++)for(let s=1;s<2**(2**m);s++){
 const U=Array.from({length:2**m},(_,i)=>i).filter(i=>s&(1<<i));
 listTests(U,m,false);abstractCubes++;
}
for(let n=4;n<=9;n++){
 const P=2**(n-1),S=Array.from({length:P},(_,i)=>i+P).filter(prime), E=[];
 for(let i=0;i<S.length;i++)for(let j=i+1;j<S.length;j++)E.push([S[i]*S[j],S[i],S[j]]);
 for(let width=1;width<=Math.min(5,n-1);width++)for(let start=0;start+width<=2*n;start+=width){
  const mask=((1<<width)-1)<<start,G=new Map();
  for(const [x,p,q] of E){
   const key=x&~mask,s=G.get(key)||[];G.set(key,s);
   for(const [y,a,b] of s){
    assert(x!==y&&((x^y)&~mask)===0&&p!==a&&p!==b&&q!==a&&q!==b,"local alternatives share factor");localPairs++;
   }
   s.push([x,p,q]);
  }
  assert(G.size<=2**(2*n-width),"outside patterns");blockChecks++;
 }
 for(const fixLow of [false,true]){
  const F=new Map();
  for(const [x,p,q] of E){
   const hi=Math.floor(x/P),lo=x%P,k=fixLow?lo:hi,v=fixLow?hi:lo;
   const row=F.get(k)||{labels:new Set(),words:[]};F.set(k,row);
   assert(!row.labels.has(p)&&!row.labels.has(q),"natural fiber factor repeat");
   row.labels.add(p);row.labels.add(q);row.words.push(v);
  }
  for(const row of F.values()){
   assert(row.words.length<=S.length/2,"row bound");
   listTests(row.words,fixLow?n+1:n-1,true);fibers++;
  }
 }
}
assert(localPairs>0&&replayChecks>0&&capacityChecks>0,"missing toy cases");
console.log({localPairs,blockChecks,fibers,abstractCubes,capacityChecks,replayChecks});