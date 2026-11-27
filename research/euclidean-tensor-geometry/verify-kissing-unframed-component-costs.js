#!/usr/bin/env node
// Exact component capacity certificates: nonnegative mass on five/seven kissing points.
// Standard Node.js; no solver or downloaded data. Optional: node this-file.js 7 3
// checks a single labelled seven-point representative. The default verifies all.
'use strict';
function sevenGraphs(){
 const n=7,E=[],idx=Array.from({length:n},()=>Array(n));for(let i=0;i<n;i++)for(let j=0;j<i;j++){idx[i][j]=idx[j][i]=1<<E.length;E.push([i,j]);}
 const S=Array.from({length:1<<n},(_,m)=>Array.from({length:n},(_,i)=>i).filter(i=>m&(1<<i)));
 const mask=a=>a.reduce((m,i,h)=>m|a.slice(0,h).reduce((p,j)=>p|idx[i][j],0),0);
 const triples=S.filter(s=>s.length===3).map(mask),four=S.filter(s=>s.length===4).map(mask),P=[];
 function perm(l,r){if(!r.length){P.push(l);return;}for(let x of r)perm([...l,x],r.filter(y=>y!==x));}perm([],S[127]);
 const seen=new Uint8Array(1<<21),out=[];for(let m=1;m<1<<21;m++){
  if(seen[m]||triples.some(v=>(m&v)===v)||four.some(v=>!(m&v)))continue;
  const e=E.filter((p,i)=>m&(1<<i));for(const p of P)seen[e.reduce((b,[i,j])=>b|idx[p[i]][p[j]],0)]=1;out.push(e);
 }if(out.length!==9)throw Error('isomorphism census');return out;
}
const GS=sevenGraphs();const B=1024,den=1000000,wt=160;
// Cycle bounds used below: sum s_e <= 3, 4.046, 5.001, 5.923.
// The only non-obvious rounding is the seven-cycle. Its two smallest Fourier
// cosines are roots of 8x^3+4x^2-4x-1, isolated by these brackets.
const cub=t=>8n*t**3n+4_000_000n*t*t-4_000_000_000_000n*t-1_000_000_000_000_000_000n;
if(cub(-900970n)*cub(-900968n)>=0n||cub(-222522n)*cub(-222520n)>=0n||
 (750000000000n+900970n*222522n)*7000n>=5923n*1000000n*(900968n+222520n))throw Error('cycle spectral rounding');
function solve(G,goal,stop=300000){
 const n=1+Math.max(...G.flat()),E=G.map(([i,j])=>[i,j]),L=E.length,id=Array.from({length:n},()=>Array(7).fill(-1));
 E.forEach(([i,j],e)=>id[i][j]=id[j][i]=e);
 let cycles=[],sets=[],seen=new Set,ord=[];let grp=[];function per(p,S){if(!S.length){if(E.every(([i,j])=>id[p[i]][p[j]]>=0))grp.push(E.map(([i,j])=>id[p[i]][p[j]]));return;}for(let x of S)per([...p,x],S.filter(i=>i!=x));}per([],Array.from({length:n},(_,i)=>i));for(let i=0;i<L;i++){for(let j of new Set(grp.map(g=>g[i])))if(i!==j)ord.push([i,j]);grp=grp.filter(g=>g[i]===i);}
 for(let i=0;i<n;i++){let adj=E.map((a,e)=>a.includes(i)?e:-1).filter(e=>e>=0);for(let m=1;m<(1<<adj.length);m++){let s=adj.filter((e,k)=>m&(1<<k));if(s.length>=2)sets.push(s);}}
 function walk(p,eds){
  if(p.length>=4&&id[p[0]][p.at(-1)]>=0){let A=[...eds,id[p[0]][p.at(-1)]],k=A.length,nm=A.slice().sort((a,b)=>a-b).join();
   if(!seen.has(nm)){seen.add(nm);cycles.push([A,({4:3000,5:4046,6:5001,7:5923})[k]])}}
  for(let j=0;j<n;j++)if(!p.includes(j)&&id[p.at(-1)][j]>=0)walk([...p,j],[...eds,id[p.at(-1)][j]])}
 for(let i=0;i<n;i++)walk([i],[]);
 const val=Array.from({length:B+1},(_,j)=>Number((BigInt(den)*(4n*BigInt(j)**4n-BigInt(j)**2n*BigInt(B)**2n)+4n*BigInt(B)**4n-1n)/(4n*BigInt(B)**4n)));
 const K=1024;let ang=Array(B+1).fill(K);const denx=BigInt(106*K);for(let k=0;k<=K;k++){const x=BigInt(111*k),d=denx,D8=40320n*d**8n,W=D8-20160n*x*x*d**6n+1680n*x**4n*d**4n-56n*x**6n*d*d+x**8n;let j=Number((W*BigInt(B)+D8-1n)/D8);for(;j<=B&&ang[j]===K;j++)ang[j]=k;}// Integer arithmetic in feasibility, rounded-up costs, score and witnesses stays below 2^53.
 let nodes=0,failed=null,solved=0,empty=0,prop=0,maxDepth=0;
 function feas(lo){for(const s of sets){let x=0,xx=0,m=B,d=s.length;for(let e of s){x+=lo[e];xx+=lo[e]**2;m=Math.min(m,lo[e]);}if((d+1)*m>=x && 2*((d+1)*xx-x*x)>(d+1)*B*B)return false;}
 for(const [S,h]of cycles){let x=0;for(let e of S)x+=lo[e];if(1000*x>B*h)return false;if(S.length%2&&S.reduce((z,e)=>z+ang[lo[e]],0)<3*K)return false;}return true;}
 function check(hi,init){
 let M=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i==j?750000:id[i][j]>=0?val[hi[id[i][j]]]:0));
 let W=init.slice(),Y=M.map(r=>r.reduce((s,v,j)=>s+v*W[j],0));let cost=W.reduce((s,w,j)=>s+w*Y[j],0);
 for(let it=0;it<100;it++){if(cost<=goal*wt**2)return [true,W,cost/den/wt**2];let best=0,mv=null;for(let i=0;i<n;i++)if(W[i])for(let j=0;j<n;j++)if(Y[i]>Y[j]){let D=1500000-2*M[i][j],a=D?Math.min(W[i],Math.max(1,Math.round((Y[i]-Y[j])/D))):W[i];let gain=2*a*(Y[i]-Y[j])-a*a*D;if(gain>best){best=gain;mv=[i,j,a];}}if(!mv)break;let[i,j,a]=mv;W[i]-=a;W[j]+=a;for(let k=0;k<n;k++)Y[k]+=a*(M[k][j]-M[k][i]);cost-=best;}return [cost<=goal*wt**2,W,cost/den/wt**2];}
 const first=Array.from({length:n},(_,i)=>Math.floor(wt/n)+(i<wt%n?1:0));
 function go(lo,hi,W,d){
  if(failed)return;nodes++;maxDepth=Math.max(maxDepth,d);if(nodes>stop){failed=['time',d];return;}for(let p=0;p<L;p++){let change=false;for(let [i,j]of ord){if(hi[i]<lo[j]){empty++;return;}if(hi[j]>hi[i]){hi[j]=hi[i];change=true;}if(lo[i]<lo[j]){lo[i]=lo[j];change=true;}}if(!change)break;}if(!feas(lo)){empty++;return;}
  for(let e=0;e<L;e++)if(hi[e]>lo[e]){let h=hi[e],l=lo[e],t=lo[e];lo[e]=h;if(!feas(lo)){while(l+1<h){let m=(l+h)>>1;lo[e]=m;if(feas(lo))l=m;else h=m;}hi[e]=h;prop++;}lo[e]=t;}
  let [ok,X,v]=check(hi,W);if(ok){solved++;return;}[ok,X,v]=check(hi,first);if(ok){solved++;return;}
  let cand=lo.map((l,i)=>hi[i]-l>1?(hi[i]-l)*(hi[i]+.2*B)*(1+.1*Math.min(X[E[i][0]],X[E[i][1]])):0);
  let e=cand.indexOf(Math.max(...cand));if(cand[e]<=0){failed=['point',lo,hi,X,v];return;}
  let m=(lo[e]+hi[e])>>1,H=hi.slice(),A=lo.slice();H[e]=A[e]=m;go(lo.slice(),H,X,d+1);go(A,hi.slice(),X,d+1);}
 go(Array(L).fill(B/2),Array(L).fill(B),first,0);return {nodes,solved,empty,prop,maxDepth,failed};}
const args=process.argv.slice(2);function one(lab,g,goal){
 const r=solve(g,goal,5000000);console.log(lab,JSON.stringify(r));if(r.failed)throw Error('unverified capacity '+lab);
}
if(!args.length||args[0]==='5')one('C5',[[0,1],[1,2],[2,3],[3,4],[4,0]],260000);
if(!args.length||args[0]==='7')for(let i=0;i<GS.length;i++)if(args.length<2||+args[1]===i)one('G7-'+i,GS[i],209000);
