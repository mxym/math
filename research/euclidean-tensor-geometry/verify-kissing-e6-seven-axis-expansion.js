'use strict';const ix=[0,1,2,3,4,5],G=ix.map(i=>ix.map(j=>i===j?2:((i<5&&j<5&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===5))?-1:0));const dot=(a,b)=>a.reduce((s,t,i)=>s+t*b[i],0);
const roots=ix.map(i=>ix.map(j=>+(i===j))),known=new Set(roots.map(r=>r.join()));for(const r of roots)for(const i of ix){const s=r.slice();s[i]-=dot(r,G[i]);if(!known.has(s.join())){known.add(s.join());roots.push(s);}}
const T=roots.filter(v=>v.every(t=>t>=0));const P=T.map(r=>T.map(v=>dot(r,G.map(g=>dot(g,v)))));
const P0=T,Q=P; // positive root coefficients and their 36x36 Gram matrix
const T1=[];for(const [i,r] of P0.entries())for(const [j,s] of P0.entries()){
 const D=2*r[5]*s[5]+3*(r[3]-r[5])*(s[3]-s[5]),C=4*Q[i][j]-D,E=r[3]*s[5]-r[5]*s[3];T1.push({i,j,C,D,E});}

const abs=z=>z<0n?-z:z,sg=z=>z<0n?-1:z>0n?1:0;function gcd(a,b){return b?gcd(b,a%b):abs(a);}
const rat=(p,q=1n)=>{if(!q)throw Error('zero denominator');const g=gcd(p,q)*(q<0n?-1n:1n);return {p:p/g,q:q/g};};
const rk=r=>r.q?r.p+'/'+r.q:[r.a,r.b,r.c,r.s].join(':');
function comp(r,p,q=1n){ // sign(r-p/q) with q normalized positive.
 if(q<0n)return comp(r,-p,-q);if(r.q)return sg(r.p*q-p*r.q);
 const x=-r.b*q-2n*r.a*p,s=r.s;if(sg(x)===s||!x)return s;
 return s*sg(q*q*r.dis-x*x);
}
function addRoot(a,b,c){
 if(!a)return b?[rat(-c,b)]:[];const g=gcd(gcd(a,b),c)*(a<0n?-1n:1n);a/=g;b/=g;c/=g;
 const dis=b*b-4n*a*c;if(dis<0n)return [];let sq=0n;while((sq+1n)**2n<=dis)sq++;
 if(sq*sq===dis)return [-1n,1n].map(k=>rat(-b+k*sq,2n*a));
 return [-1,1].map(s=>({a,b,c,s,dis}));
}
function coeff({C,D,E},t){return [BigInt(C-t-D),BigInt(12*E),BigInt(6*(C-t+D))];}
const roots1=new Map();for(const v of T1)for(const t of [-8,-4,4,8])for(const r of addRoot(...coeff(v,t)))if(comp(r,0n)>=0)roots1.set(rk(r),r);

// Isolate and order every algebraic endpoint with verified separating rational intervals.
function floorAt(r,den){let hi=1n;while(comp(r,hi,den)>=0)hi*=2n;let lo=0n;while(lo+1n<hi){const mid=(lo+hi)/2n;if(comp(r,mid,den)>=0)lo=mid;else hi=mid;}return lo;}
let den=1n,end;for(;;den*=2n){end=[...roots1.values()].map(r=>[r,floorAt(r,den)]).sort((a,b)=>sg(a[1]-b[1]));if(end.every((r,i)=>!i||r[1]-end[i-1][1]>=2n))break;}
function signAt(y,v,t){
 const [a,b,c]=coeff(v,t);if(!y)return sg(a);if(y.q)return sg(a*y.p*y.p+b*y.p*y.q+c*y.q*y.q);
 const u=b*y.a-a*y.b,z=c*y.a-a*y.c;if(!u)return sg(z);return sg(u)*comp(y,-z,u);
}
function test(y){const edges=Array.from({length:72},()=>[]);let common=0;
 for(const v of T1){let s;if(signAt(y,v,4)>0)s=-1;else if(signAt(y,v,-4)<0)s=1;else continue;
 if(signAt(y,v,-8*s)===0){s=-s;common++;}
 edges[v.i].push([36+v.j,s]);edges[36+v.j].push([v.i,s]);}
 const signs=new Int8Array(72);let ok=true;for(let i=0;i<72;i++)if(!signs[i]){signs[i]=1;const q=[i];for(let k=0;k<q.length;k++)for(const [v,s] of edges[q[k]]){if(!signs[v]){q.push(v);signs[v]=s*signs[q[k]];}else if(signs[v]!==s*signs[q[k]])ok=false;}}
 return [ok,common];
}
const records=[];let ok=0;for(const [[r,f],i] of end.map((x,i)=>[x,i])){const z=test(r),w=test(rat(f+1n,den));if(w[0])throw Error('possible open interval '+i);if(z[0]){records.push([rk(r),z]);ok++;}if(z[0]&&z[1]!==20&&z[1]!==36)throw Error('unexpected eligible angle');}
const last=test(null);if(last[0]&&![20,36].includes(last[1]))throw Error('infinity');console.log(end.length,records,last,String(den));
if(end.length!==14||JSON.stringify(records)!=='[["0/1",[true,36]]]'||JSON.stringify(last)!=='[true,20]')throw Error('atlas census');
const signed=new Map(roots.map((r,i)=>[r.join(),i]));
const gen=[...ix.map(k=>roots.map(r=>{const z=r.slice();z[k]-=dot(G[k],r);return signed.get(z.join());})),roots.map(r=>signed.get([r[4],r[3],r[2],r[1],r[0],r[5]].join()))];
const needed=[];for(let a=0;a<6;a++)for(let b=0;b<6;b++)for(let c=0;c<6;c++)for(let d=0;d<6;d++){if(new Set([a,b,c,d]).size<4)continue;if(G[a][b]===-1&&G[b][c]===-1&&!G[a][c]&&!G[a][d]&&!G[b][d]&&!G[c][d])needed.push([a,b,c,d]);}
const queue=[[0,1,2,4]],seenB=new Set(queue.map(x=>x.join()));for(const u of queue)for(const g of gen){const v=u.map(i=>g[i]),k=v.join();if(!seenB.has(k)){seenB.add(k);queue.push(v);}}
if(needed.length!==8||queue.length!==51840||needed.some(v=>!seenB.has(v.join())))throw Error('parabolic flags');
if(!P0.some(r=>r.join()==='1,2,3,2,1,2'))throw Error('normal root');
const W=[1,2,3,2,1,2],Z=[0,0,0,1,0,-1],u=[0,0,0,0,0,1];if(String(G.map(g=>dot(g,W)))!==String(u))throw Error('weight five');
// For every A2 root pair the six perpendicular axes form two components of three A2 axes.
let a2count=0;for(let i=0;i<P0.length;i++)for(let j=i+1;j<P0.length;j++)if(Math.abs(Q[i][j])===1){const S=Q[i].map((q,r)=>!q&&!Q[j][r]?r:-1).filter(r=>r>=0);if(S.length!==6)throw Error('A2 perpendicular size');const components=[];const seen=new Set();for(const k of S)if(!seen.has(k)){const C=[k];seen.add(k);for(const t of C)for(const f of S)if(!seen.has(f)&&Q[t][f]){seen.add(f);C.push(f);}components.push(C);}if(components.length!==2||components.some(c=>c.length!==3||c.some(t=>c.some(f=>!Q[t][f]))))throw Error('bad pair');a2count++;}
console.log('A2 pairs',a2count,' A3+A1 ordered flags',queue.length);

const threeV=[1,2,3,4,2,0];if(String(G.map(g=>dot(g,threeV)))!=='0,0,0,3,0,-3'||dot(threeV,G.map(g=>dot(g,threeV)))!==12||dot(W,G.map(g=>dot(g,threeV)))!==0)throw Error('normal Gram matrix');
for(let code=0;code<243;code++){let x=code;const n=[];for(let i=0;i<5;i++){n.push(x%3);x=Math.floor(x/3);}let m=0;for(let i=0;i<5;i++)for(let j=0;j<i;j++)m+=Math.max(n[i],n[j]);if(n.reduce((a,b)=>a+b,0)>=6&&m<=13)throw Error('signed centers');}
for(let r=1;r<=5;r++)for(let m=0;m<=13;m++){const k=m+ r*(r-1)/2-4*r;if(k<4)continue;if(r>=4)throw Error('four centers and eight missing at one');if(r===3&&m-13!==0)throw Error('three centers with one full');}
for(let e=0;e<=3;e++)for(let r=0;r<=5;r++){const saving=r===5?1:0;if(1+2*r+e-saving>10+e)throw Error('noncenter count');}
