'use strict';
// Size-65 layered classification; F_13, exact integer arithmetic throughout.
const p=13,mod=x=>(x%p+p)%p;
const inv=Array.from({length:p},(_,x)=>Array.from({length:p},(_,y)=>y).find(y=>mod(x*y)===1));
const chk=(x,msg)=>{if(!x)throw Error(msg);};
const bin=[];for(let i=0;i<=7;i++)bin[i]=Array.from({length:i+1},(_,j)=>j===0||j===i?1:bin[i-1][j]+bin[i-1][j-1]);
const pw=Array.from({length:p},(_,x)=>Array.from({length:10},(_,i)=>mod(x**i)));
const code=a=>a.reduce((s,x)=>p*s+x,0);
const dec=(n,k)=>Array.from({length:k},(_,i)=>Math.floor(n/p**(k-1-i))%p);
const pm=(a,b)=>Array.from({length:a.length+b.length-1},(_,i)=>mod(a.reduce((s,x,j)=>s+x*(b[i-j]??0),0)));
const plus=(a,b,c=1)=>a.map((x,i)=>mod(x+c*b[i]));
const graphs=[];let trials=0,parabolas=0;
for(let d=2;d<=9;d++){
 const a=Array(d+1).fill(0);a[d]=1;
 function enumA(i){
  if(i<d-1){for(let r=0;r<p;r++){a[i]=r;enumA(i+1);}return;}
  trials++;
  for(const k of [11,12]){
   let q=0;for(let j=2;j<=d;j++)if(k-j>=2&&k-j<=d)q+=a[j]*a[k-j];
   if(mod(q))return;
  }
  const f=pw.map(row=>mod(a.reduce((s,x,j)=>s+x*row[j],0)));
  if(mod(f.reduce((s,x)=>s+x**3,0)))return;
  for(let s=0;s<p;s++){
   const c=new Uint8Array(p);
   for(let x=0;x<p;x++)if(++c[mod(f[x]-s*x)]>5)return;
  }
  const M=[];for(let k=4;k<=7;k++)M[k]=Array.from({length:k+1},(_,j)=>mod(bin[k][j]*f.reduce((s,y,x)=>s+pw[x][k-j]*pw[y][j],0)));
  if(M[4].every(x=>x===0)){chk(d===2,'quartic-zero graph not parabolic');parabolas++;return;}
  graphs.push({f,M});
 }
 enumA(2);
}
chk(trials===5229044&&parabolas===1&&graphs.length===2158,'local graph census');
console.log({trials,parabolas,nonzeroQuarticGraphs:graphs.length});
function transform(P,s,t,u){
 const k=P.length-1;
 return P.map((_,b)=>mod(P.slice(0,b+1).reduce((z,x,j)=>z+x*bin[k-j][b-j]*pw[s][k-b]*pw[t][j]*pw[u][b-j],0)));
}
const canonical=new Map();
const proj=q=>{const c=q.find(x=>x);return code(q.map(x=>mod(x*inv[c])));};
function rep(q){
 const h=proj(q);if(canonical.has(h))return canonical.get(h);
 const all=[];for(let t=1;t<p;t++)for(let u=0;u<p;u++)all.push(proj(transform(q,1,t,u)));
 const r=Math.min(...all);for(const k of all)canonical.set(k,r);return r;
}
const raw=new Map(); // quartic line -> amplitude -> canonical fifth moment -> ST signature -> graphs
for(const {f,M} of graphs){
 const id=rep(M[4]);if(!raw.has(id))raw.set(id,new Map());
 const levels=raw.get(id);
 for(let s=1;s<p;s++)for(let t=1;t<p;t++)for(let u=0;u<p;u++){
  const Q=transform(M[4],s,t,u);if(proj(Q)!==id)continue;
  const k=Q.findIndex(x=>x),c=Q[k], R=transform(M[5],s,t,u),S=transform(M[6],s,t,u),T=transform(M[7],s,t,u);
  const l=[mod(-R[k]*inv[mod(5*c)]),0];
  l[1]=mod(-plus(R,pm(Q,l),5)[k+1]*inv[mod(5*c)]);
  const ll=pm(l,l), r=plus(R,pm(Q,l),5), a=plus(plus(S,pm(R,l),6),pm(Q,ll),15);
  const b=plus(plus(plus(T,pm(S,l),7),pm(R,ll),21),pm(Q,pm(l,ll)),35);
  const key=code(r),sig=code(a)+','+code(b);
  if(!levels.has(c))levels.set(c,new Map());const d=levels.get(c);
  if(!d.has(key))d.set(key,new Map());const q=d.get(key);
  if(!q.has(sig))q.set(sig,{a,b,graphs:new Map()});const g=q.get(sig).graphs;
  const h=[];f.forEach((v,x)=>h[mod(s*x+l[0])]=mod(t*v+u*x+l[1]));g.set(code(h.slice(0,7))+','+code(h.slice(7)),h);
 }
}
chk(raw.size===22,'quartic orbit count');
const cs=[], seen=new Set();
function subsets(i,n,xs){
 if(n){for(let j=i;j<=p-n;j++)subsets(j+1,n-1,xs.concat(j));return;}
 if(seen.has(xs.join(',')))return;
 cs.push(xs);for(let s=1;s<p;s++)for(let t=0;t<p;t++)seen.add(xs.map(x=>mod(s*x+t)).sort((a,b)=>a-b).join(','));
}
subsets(0,5,[]);chk(cs.length===10,'level orbit count');
const V=[];for(let y=0;y<p;y++)for(let z=0;z<p;z++)V.push([1,y,z]);for(let z=0;z<p;z++)V.push([0,1,z]);V.push([0,0,1]);
const dot=(x,y)=>mod(x.reduce((s,t,i)=>s+t*y[i],0));
const L=V.map(x=>V.flatMap((y,i)=>dot(x,y)===0?[i]:[]));
const idOf=([x,y,z])=>x?p*mod(y*inv[x])+mod(z*inv[x]):y?p*p+mod(z*inv[y]):p*p+p;
let fifth=0, signatures=0, tested=0, capped=0, full=0;
function geo(z,H){
 const few=H.map(v=>[...v.graphs.values()]);
 function run(i,Y){
  if(i<5){for(const f of few[i])run(i+1,Y.concat([f]));return;}
  tested++;
  const pts=Y.flatMap((f,j)=>f.map((y,x)=>[x,y,z[j]]));
  for(const v of V){const n=new Uint8Array(p);for(const x of pts)if(++n[dot(v,x)]>p)return;}
  capped++;
  const D=new Uint8Array(V.length);
  for(let a=0;a<65;a++)for(let b=0;b<a;b++)D[idOf(pts[a].map((x,k)=>mod(x-pts[b][k])))]=1;
  if(L.some(l=>l.every(k=>D[k])))full++;else throw Error('geometrically admissible set');
 }
 run(0,[]);
}
for(const levels of raw.values())for(const z of cs){
 const lambda=z.map(x=>inv[z.filter(y=>y!==x).reduce((v,y)=>mod(v*(x-y)),1)]);
 for(let A=1;A<p;A++){
  const w=lambda.map(x=>mod(x*A)), d=w.map(c=>levels.get(c));if(d.some(v=>!v))continue;
  const X=d.map((m,i)=>new Map([...m].map(([r,v])=>[code(dec(r,6).map(x=>mod(x*inv[w[i]]))),v])));
  for(const [q0,m0] of X[0])for(const [q1,m1] of X[1]){
   const a=dec(q0,6), b=dec(q1,6).map((x,i)=>mod((x-a[i])*inv[mod(z[1]-z[0])]));
   const m=[m0,m1,...z.slice(2).map((x,i)=>X[i+2].get(code(a.map((v,j)=>mod(v+(x-z[0])*b[j])))))];
   if(m.some(v=>!v))continue;fifth++;
   const opts=m.map((m,i)=>[...m.values()].map(h=>({h,v:h.a.concat(h.a.map(x=>mod(z[i]*x)),h.b)})));
   const ix=[0,1,2,3,4].sort((x,y)=>opts[x].length-opts[y].length);
   const map=new Map();
   for(const a of opts[ix[3]])for(const b of opts[ix[4]]){const k=plus(a.v,b.v).join(',');if(!map.has(k))map.set(k,[]);map.get(k).push([a.h,b.h]);}
   for(const a of opts[ix[0]])for(const b of opts[ix[1]])for(const c of opts[ix[2]]){
    const k=plus(plus(a.v,b.v),c.v).map(x=>mod(-x)).join(',');
    for(const other of map.get(k)??[]){signatures++;const H=[];[a.h,b.h,c.h,...other].forEach((h,j)=>H[ix[j]]=h);geo(z,H);}
   }
  }
 }
}
chk(fifth===15240&&signatures===1140&&tested===1944&&capped===456&&full===456,'global list counts');
console.log({quarticOrbits:raw.size,fifth,signatures,tested,capped,full});