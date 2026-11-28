#!/usr/bin/env node
// |C5| continuous arc localization. Node standard library only.
'use strict';
const K=4096,B=65536,D=10000000,W0=360,goal=D/4;
const piL=3141592653589793n,piU=piL+1n,unit=1000000000000000n,denA=3n*BigInt(K)*unit;
const low=[],high=[];const fact=n=>n<2?1n:BigInt(n)*fact(n-1);const d=denA,dd=d*d,scale=fact(26)*d**26n;
// Machin's identity and alternating arctangent-series brackets.
const sum=(x,y)=>[x[0]*y[1]+y[0]*x[1],x[1]*y[1]], sc=(k,x)=>[k*x[0],x[1]], cmp=(x,y)=>x[0]*y[1]-y[0]*x[1];
function atan(q){let x=[0n,1n];for(let i=0;i<16;i++)x=sum(x,[(i%2?-1n:1n),BigInt(2*i+1)*q**BigInt(2*i+1)]);return [x,sum(x,[1n,33n*q**33n])];}
const [l5,h5]=atan(5n),[l239,h239]=atan(239n);
if(cmp(sum(sc(16n,l5),sc(-4n,h239)),[piL,unit])<=0n||cmp(sum(sc(16n,h5),sc(-4n,l239)),[piU,unit])>=0n)throw Error('pi bracket');
let c=Array.from({length:14},(_,k)=>(k%2?-1n:1n)*fact(26)/fact(2*k)*d**BigInt(26-2*k)), div=(a,b)=>a>=0n?a/b:-((-a+b-1n)/b);
for(let j=0;j<=3*K;j++){let zj=BigInt(j), xl=(zj*piL)**2n,xu=(zj*piU)**2n,lo=0n,hi=0n;
 for(let k=13;k>=0;k--)lo=lo*xu+c[k];
 for(let k=12;k>=0;k--)hi=hi*xl+c[k];
 low[j]=Math.max(-B,Number(div(lo*BigInt(B),scale)));high[j]=Math.min(B,-Number(div(-hi*BigInt(B),scale)));}
const f=[],g=[],dg=[];for(let i=0;i<=B;i++){let x=BigInt(i),b=BigInt(B),n=BigInt(D)*(4n*x**4n-x*x*b*b);f[i]=-Number(div(-n,4n*b**4n));}
for(let i=0;i<=K;i++){g[i]=f[high[i]];let si=low[Math.abs(3*K/2-2*i)],co=low[2*i];
 let num=BigInt(D)*piL*BigInt(Math.max(0,si))*BigInt(3*B+4*co);
 dg[i]=Number(num/(12n*BigInt(K)*unit*BigInt(B)**2n));}
const cyc=[0,1,2,3,4],E=cyc.map(i=>[i,(i+1)%5]),P=cyc.map(i=>[i,(i+2)%5]),T=12544,limit=10000000;
const perm=cyc.flatMap(r=>[1,-1].map(d=>cyc.map(i=>(r+d*i+10)%5)));let grp=perm,ord=[];
for(let i=0;i<5;i++){for(let j of new Set(grp.map(g=>g[i])))if(i!==j)ord.push([i,j]);grp=grp.filter(g=>g[i]===i);}
function setupMix(){const n=5, den=D,wt=W0,val=f;const plist=[];const ind=Array.from({length:n},()=>Array(n).fill(-1));for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){ind[i][j]=ind[j][i]=plist.length;plist.push([i,j]);}
function neig(X){const a=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?1:X[ind[i][j]])),V=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>+(i===j)));
 for(let loop=0;loop<14;loop++){let peak=0;for(let p=0;p<n;p++)for(let q=p+1;q<n;q++){let z=a[p][q];peak=Math.max(peak,Math.abs(z));if(Math.abs(z)<1e-10)continue;
 let tau=(a[q][q]-a[p][p])/(2*z),t=(tau>=0?1:-1)/(Math.abs(tau)+Math.hypot(1,tau)),c=1/Math.hypot(1,t),s=t*c;a[p][p]-=t*z;a[q][q]+=t*z;a[p][q]=a[q][p]=0;
 for(let k=0;k<n;k++){if(k!==p&&k!==q){let b=a[k][p],d=a[k][q];a[k][p]=a[p][k]=c*b-s*d;a[k][q]=a[q][k]=s*b+c*d;}let b=V[k][p],d=V[k][q];V[k][p]=c*b-s*d;V[k][q]=s*b+c*d;}}
 if(peak<1e-9)break;}let neg=[];for(let k=0;k<n;k++)if(a[k][k]<-1e-12)neg.push(V.map(row=>Math.sqrt(-a[k][k])*row[k]));return neg;}
const mixcache=[];let nMix=0,nHit=0;
function asLines(l,u){let bs=[],ss=[];for(let p=0;p<l.length;p++){let L=l[p],U=u[p],a=val[Math.abs(L)],b=val[Math.abs(U)],s=0,c;
 if(U>L&&(L>=.21*B||U<=-.21*B)){s=Math.trunc((b-a)/(U-L));c=Math.max(a-s*L,b-s*U);}else c=L<=0&&U>=0?Math.max(0,a,b):Math.max(a,b);
 ss[p]=s;bs[p]=c;}return [bs,ss];}
const TWT=420, QWT=den*TWT*TWT, FGR=262144, RMT=10000000;
function capLine(W,lines){let[bs,ss]=lines,o=(3*den/4)*W.reduce((s,w)=>s+w*w,0)-goal*TWT*TWT,c=[];for(let p=0;p<plist.length;p++){let[i,j]=plist[p],v=2*W[i]*W[j];o+=v*bs[p];c.push(v*ss[p]);}
 return {W,o,c,z:o/QWT,a:c.map(v=>v*B/QWT),get norm(){return Math.max(.01,Math.hypot(...this.a));}};}
function findW(y,lines,start){
 let[bs,ss]=lines,W=start.slice(),A=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?.75:(bs[ind[i][j]]+B*y[ind[i][j]]*ss[ind[i][j]])/den));
 let v=A.map(row=>row.reduce((x,b,j)=>x+b*W[j],0));for(let it=0;it<100;it++){let best=0,mv;for(let i=0;i<n;i++)if(W[i])for(let j=0;j<n;j++)if(v[i]>v[j]){let D=Math.max(0,1.5-2*A[i][j]),k=D?Math.min(W[i],Math.max(1,Math.round((v[i]-v[j])/D))):W[i],g=2*k*(v[i]-v[j])-k*k*D;if(g>best){best=g;mv=[i,j,k];}}
 if(!mv)break;let[i,j,k]=mv;W[i]-=k;W[j]+=k;for(let h=0;h<n;h++)v[h]+=k*(A[h][j]-A[h][i]);}return W;}
function recordCut(ob){if(ob.W.some(v=>v.some(x=>!Number.isSafeInteger(x)||x<0)||v.reduce((s,x)=>s+x,0)!==TWT)||ob.mu.some(x=>!Number.isSafeInteger(x)||x<0))throw Error("mass");const T=BigInt(FGR)**2n*BigInt(B),J=BigInt(RMT)*BigInt(QWT),mu=ob.mu.map(BigInt),W=ob.W.map(a=>a.map(BigInt)),F=ob.F.map(a=>a.map(BigInt));
 let d=BigInt(B)*J*F.reduce((a,y)=>a+y.reduce((s,w)=>s+w*w,0n),0n),T2=BigInt(TWT)**2n;
 for(let k=0;k<W.length;k++)d+=T*mu[k]*(BigInt(3*den/4)*W[k].reduce((s,w)=>s+w*w,0n)-BigInt(goal)*T2);
 let h=plist.map(([i,j])=>2n*J*F.reduce((a,v)=>a+v[i]*v[j],0n)),p=plist.map(([i,j])=>2n*T*W.reduce((s,v,k)=>s+mu[k]*v[i]*v[j],0n));
 const sc=Number(BigInt(B)*BigInt(FGR)**2n*J);return {d,h,p,dN:Number(d)/sc,hN:h.map(v=>Number(v)/sc),pN:p.map(v=>Number(v)/sc)};}
function fastMix(ob,lines,l,u){let c=ob.dN;for(let i=0;i<l.length;i++){let p=ob.pN[i],v=ob.hN[i]+p*lines[1][i];c+=p*lines[0][i]+v*(v>0?u[i]:l[i]);}
 if(c> -1e-13)return false;let z=ob.d;for(let i=0;i<l.length;i++){let p=ob.p[i],v=ob.h[i]+p*BigInt(lines[1][i]);z+=p*BigInt(lines[0][i])+v*BigInt(v>0n?u[i]:l[i]);}return z<0n;}
function cmix(l,u,lines){for(let j=0;j<mixcache.length;j++)if(fastMix(mixcache[j],lines,l,u)){nHit++;if(j>0){let b=mixcache.splice(j,1)[0];mixcache.unshift(b);}return true;}return false;}

function checkedMix(l,u,Wi,limit){
 let lines=asLines(l,u);if(cmix(l,u,lines))return true;
 let ls=[],seen=new Set;function add(W){let key=W.join();if(!seen.has(key)){seen.add(key);ls.push(capLine(W,lines));}}
 let uni=Wi.map((v,i)=>Math.floor(TWT/n)+(i<TWT%n?1:0)),start=Wi.map(w=>Math.round(TWT*w/wt));start[start.indexOf(Math.max(...start))]+=TWT-start.reduce((a,b)=>a+b,0);add(start);add(uni);
 let x=l.map((z,j)=>(z+u[j])/(2*B)),old=x.slice();for(let it=0;it<limit;it++){let y=x.map((v,j)=>v+it/(it+3)*(v-old[j])),fac=neig(y),H=plist.map(([i,j])=>2*fac.reduce((a,v)=>a+v[i]*v[j],0)),tr=fac.reduce((a,v)=>a+v.reduce((s,w)=>s+w*w,0),0);
 if(it%12===0&&ls.length<30){add(findW(y,lines,uni));add(findW(y,lines,start));}let grad=H.slice(),mu=[],c=tr;
 for(let g of ls){let d=g.z+g.a.reduce((v,w,p)=>v+w*y[p],0),lm=Math.max(0,-d)/g.norm**2;mu.push(lm);c+=lm*g.z;for(let p=0;p<grad.length;p++)grad[p]+=lm*g.a[p];}
 c+=grad.reduce((a,v,p)=>a+v*(v>0?u[p]:l[p])/B,0);
 if(c< -1e-10){const F=fac.map(v=>v.map(z=>Math.round(z*FGR))),good=mu.map((v,i)=>Math.round(v*RMT)>0?i:-1).filter(i=>i>=0),sp=good.map(i=>Math.round(mu[i]*RMT));if(sp.every(v=>Number.isSafeInteger(v)&&v>=0)){
 const W=good.map(i=>ls[i].W),ob={F,mu:sp,W,h:plist.map(([i,j])=>2*F.reduce((a,v)=>a+v[i]*v[j],0)/FGR**2),diag:F.reduce((a,v)=>a+v.reduce((s,w)=>s+w*w,0),0)/FGR**2};
 let rigor=recordCut(ob);if(fastMix(rigor,lines,l,u)){mixcache.unshift(rigor);if(mixcache.length>150)mixcache.pop();nMix++;return true;}}}
 old=x;x=y.map((v,p)=>Math.max(l[p]/B,Math.min(u[p]/B,v+grad[p]/(2+ls.length))));}
 return false;}


return function(bds,l,u,W,last,wide,nodes){let a=[],b=[];for(let i of cyc){let k=ind[E[i][0]][E[i][1]],j=ind[P[i][0]][P[i][1]];a[k]=-high[l[i]];b[k]=-low[u[i]];[a[j],b[j]]=bds[i];}
if(mixcache.length&&cmix(a,b,asLines(a,b)))return true;
if(last || wide<=128&&nodes%71===0) return checkedMix(a,b,W,last?1600:80);return false;};}
const mix=setupMix();
let n=0,empty=0,sol=0,mixN=0,fail=null;
function go(l,u,W,depth){if(fail)return;if(++n>limit){fail=['time',depth];return;}
 for(let pass=0;pass<15;pass++){let change=false;
 let total=u.reduce((a,b)=>a+b,0);
 for(let i of cyc){let v=Math.max(l[i],T-total+u[i],K-u[(i+1)%5],K-u[(i+4)%5]);if(v>u[i]){empty++;return;}if(v>l[i]){l[i]=v;change=true;}}
 for(let [i,j]of ord){if(l[i]>u[j]){empty++;return;}if(l[j]<l[i]){l[j]=l[i];change=true;}if(u[i]>u[j]){u[i]=u[j];change=true;}}if(!change)break;}
 let A=Array.from({length:5},()=>Array(5).fill(.75*D)),bounds=[];
 for(let i of cyc){let [a,b]=E[i];A[a][b]=A[b][a]=g[l[i]];
 let [p,q]=P[i],j=(i+1)%5,h=Math.max(-B/2,low[u[i]+u[j]]),v=Math.min(B/2,-low[u[(i+2)%5]+u[(i+3)%5]+u[(i+4)%5]]);
 if(h>v){empty++;return;}bounds.push([h,v]);let z=Math.max(f[Math.abs(h)],f[Math.abs(v)],h<=0&&v>=0?0:-Infinity);A[p][q]=A[q][p]=z;}
 const sets=[[cyc,T-l.reduce((a,b)=>a+b,0)],...cyc.map(i=>[[i,(i+1)%5],K-l[i]-l[(i+1)%5]])].filter(p=>p[1]>0);
 function opt(W){
  W=W.slice();let pot=A.map(row=>row.reduce((s,v,j)=>s+v*W[j],0)),cost=W.reduce((s,w,i)=>s+w*pot[i],0);
  for(let it=0;it<55;it++){if(cost<=goal*W0**2)return [true,W];let best=0,t;
   for(let i of cyc)if(W[i])for(let j of cyc)if(pot[i]>pot[j]){let dv=2*(.75*D-A[i][j]),k=dv?Math.min(W[i],Math.max(1,Math.round((pot[i]-pot[j])/dv))):W[i],gain=2*k*(pot[i]-pot[j])-k*k*dv;
   if(gain>best){best=gain;t=[i,j,k];}}if(!t)break;let[i,j,k]=t;W[i]-=k;W[j]+=k;cost-=best;for(let a of cyc)pot[a]+=k*(A[a][j]-A[a][i]);}
  let grad=cyc.map(i=>2*W[i]*W[(i+1)%5]*Math.min(dg[l[i]],dg[u[i]]));
  let need=cost-goal*W0**2;
  for(let it=0;it<6;it++){let best=0,bi=null,bv;for(let [ids,amount]of sets){let v=Math.min(...ids.map(i=>grad[i]));if(v*amount>best){best=v*amount;bi=ids;bv=v;}}if(!bi)break;need-=best;if(need<=0)return [true,W];for(let i of bi)grad[i]-=bv;}
  return [need<=0,W];}
 let [ok,V]=opt(W);if(!ok)[ok,V]=opt(Array(5).fill(W0/5));if(ok){sol++;return;}
 let widths=cyc.map(i=>(u[i]-l[i]>1?(u[i]-l[i])*(4*W0/5+Math.min(V[i],V[(i+1)%5])):0)),e=widths.indexOf(Math.max(...widths));
 if(mix(bounds,l,u,V,!widths[e],Math.max(...u.map((v,i)=>v-l[i])),n)){sol++;mixN++;return;}if(!widths[e]){fail=['point',l,u,V,bounds];return;}
 let mid=(l[e]+u[e])>>1,L=l.slice(),U=u.slice();L[e]=U[e]=mid;go(l.slice(),U,V,depth+1);go(L,u.slice(),V,depth+1);}
go(Array(5).fill(0),Array(5).fill(K),Array(5).fill(W0/5),0);if(fail)throw Error(JSON.stringify(fail));console.log('PASS',JSON.stringify({n,sol,empty,mixN}));
