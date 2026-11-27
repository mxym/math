'use strict';
// Exact small checks for excluding four-direction pencils at size 65.
const p=13, M=x=>(x%p+p)%p, all=Array.from({length:p},(_,i)=>i);
const I=all.map(i=>all.find(j=>M(i*j)===1));
const eq=(a,b)=>{if(JSON.stringify(a)!==JSON.stringify(b))throw Error(JSON.stringify({a,b}));};
function sub(n){
 const out=[]; function gen(i,k,S){if(!k){out.push(S);return;}for(let j=i;j<=p-k;j++)gen(j+1,k-1,S.concat(j));}
 gen(0,n,[]);return out;
}
function orbit(n){
 const seen=new Set(), reps=[];
 for(const S of sub(n)){if(seen.has(S.join(',')))continue;reps.push(S);
 for(let a=1;a<p;a++)for(const b of all)seen.add(S.map(z=>M(a*z+b)).sort((x,y)=>x-y).join(','));}
 return reps;
}
function crossCheck(){
 const pts=Array.from({length:p*p},(_,j)=>[j%p,Math.floor(j/p)]),t=[0,1,p];
 const dir=(a,b)=>{if(a===b)return -1;const [x,y]=pts[a],[u,v]=pts[b],d=M(x-u);return d?M((y-v)*I[d]):p;};
 let n=0;
 for(let s=1;s<=11;s++){
   const D=new Set([0,12,13,s]),A=pts.map((_,i)=>i).filter(i=>t.every(j=>D.has(dir(i,j))));
   for(let i=0;i<A.length;i++)for(let j=i+1;j<A.length;j++){
     if(!D.has(dir(A[i],A[j])))continue;
     const B=t.concat([A[i],A[j]]),U=new Set(B);let good=false;
     for(const c of B)for(const a of B)for(const b of B){
       const [cx,cy]=pts[c], [ax,ay]=pts[a], [bx,by]=pts[b];
       if(M((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))===0)continue;
       if(U.has(M(2*cx-ax)+p*M(2*cy-ay))&&U.has(M(2*cx-bx)+p*M(2*cy-by)))good=true;
     }
     if(!good)throw Error('noncross');n++;
   }
 }
 eq(n,6);console.log({fiveSiteCrosses:n});
}
crossCheck();
const pol=[];
for(const a of all)for(const b of all)for(const c of all)for(const d of all)
 pol.push({deg:d?5:c?4:b?3:a?2:0,v:all.map(z=>M(z*z*(a+z*(b+z*(c+z*d)))))});
const perms=[];
function perm(A,S){if(!A.length){perms.push(S);return;}A.forEach((x,j)=>perm(A.filter((_,k)=>k!==j),S.concat(x)));}
perm([1,12,5,8],[]);
const LR=(xs,z)=>xs.map((a,j)=>xs.reduce((u,b,k)=>k===j?u:M(u*(z-b)*I[M(a-b)]),1));
const sizes=[];
for(let n=0;n<=4;n++)for(const S of orbit(n)){
 const G=all.filter(z=>!S.includes(z));
 const L2=all.map(z=>LR(G.slice(0,7),z)),L3=all.map(z=>LR(G.slice(0,8),z));
 const cand=[];
 for(const {deg,v} of pol){
   const q=G.slice(0,7).map(z=>M(5*v[z]**2)),r=G.slice(0,8).map(z=>M(5*v[z]**3));
   const fold=(row,data)=>M(row.reduce((s,x,j)=>s+x*data[j],0));
   if(G.slice(7).some(z=>fold(L2[z],q)!==M(5*v[z]**2)))continue;
   if(G.slice(8).some(z=>fold(L3[z],r)!==M(5*v[z]**3)))continue;
   const c2=S.map(z=>M(fold(L2[z],q)-5*v[z]**2));
   const c3=S.map(z=>M(fold(L3[z],r)-3*v[z]*fold(L2[z],q)+10*v[z]**3));
   cand.push({deg,c2,c3});
 }
 if(n<=3){
   if(cand.length!==13||cand.some(a=>a.deg>2))throw Error('scalar mean');
 }else{
   let hit=0;
   for(const u of cand)for(const v of cand)for(const k of perms){
     if(S.some((_,j)=>M(k[j]**2*u.c2[j]-v.c2[j])||M(k[j]**3*u.c3[j]-v.c3[j])))continue;
     if(u.deg>2||v.deg>2)throw Error('large mean pair');
     hit++;
   }
   eq(hit,4056);sizes.push(cand.length);
 }
}
eq(sizes,[37,25,37,49,37,37,85]);console.log({fourLayerCandidates:sizes,pairsEach:4056});
const power=all.map(z=>{const a=[1];for(let j=0;j<12;j++)a.push(M(a.at(-1)*z));return a;});
function degree(v){for(let d=12;d>=1;d--)if(M(v.reduce((s,x,z)=>s+x*power[z][12-d],0)))return d;return 0;}
let count=0;
for(const a of all)for(const b of all)for(const c of all)for(const d of all){
 const Q=all.map(z=>M(a+z*(b+z*(c+z*d))));
 if(Q.includes(0)||degree(Q.map(x=>power[x][8]))>8||degree(Q.map(x=>power[x][9]))>10)continue;
 if(b||c||d)throw Error('nonconstant radial moment');
 count++;
}
eq(count,12);console.log({constantRadialMoments:count});