// Exact finite cross-check of labeled high-signature extraction.
const Q=3,S=6,H=3,D=2, core=[[0,1],[1,2]];
const asc=a=>a.slice().sort((x,y)=>x-y);
const key=a=>asc(a).join(',');
function parts(n,edges,mask) {
 const p=Array.from({length:n},(_,i)=>i);
 const root=x=>p[x]===x?x:root(p[x]);
 edges.forEach(([u,v],i)=>{if(mask>>i&1)p[root(u)]=root(v);});
 const M=new Map;
 for(let i=0;i<n;i++){const k=root(i),a=M.get(k)??[];a.push(i);M.set(k,a);}
 return [...M.values()];
}
function add(M,k,a=1){M.set(k,(M.get(k)??0)+a);}
function bloc(edges) {
 const a=Array.from({length:D+1},()=>new Map());
 for(let mask=0;mask<1<<edges.length;mask++){
  const P=parts(S,edges,mask),d=S-P.find(v=>v.includes(0)).length;
  if(d<=D)add(a[d],key(P.filter(v=>!v.includes(0)).map(v=>v.length)));
 }return a;
}
const parse=s=>s?s.split(',').map(Number):[];
function join(A,B) {
 const C=new Map();
 for(const [a,ca] of A)for(const [b,cb] of B)add(C,key([...parse(a),...parse(b)]),ca*cb);
 return C;
}
function cutProduct(component,Fs,d){
 let a=Array.from({length:d+1},()=>new Map());a[0].set('',1);
 for(const v of component){
  const b=Array.from({length:d+1},()=>new Map());
  for(let i=0;i<=d;i++)for(let j=0;i+j<=d;j++)
   for(const [k,c] of join(a[i],Fs[v][j]))add(b[i+j],k,c);
  a=b;
 }return a[d];
}
function labeled(p,r) {
 if(!r.length)return [[]];
 return p.flatMap((c,i)=>c.length===r[0]
    ?labeled(p.filter((_,j)=>j!==i),r.slice(1)).map(t=>[c,...t]):[]);
}
const polyKey=(hi,lo)=>key(hi)+'|'+key(lo);
const equal=(A,B)=>A.size===B.size&&[...A].every(([k,v])=>B.get(k)===v);
function check(blocks) {
 const edges=[...core.map(([u,v])=>[S*u,S*v]),...blocks.flatMap((b,i)=>b.map(([u,v])=>[S*i+u,S*i+v]))], U=new Map();
 for(let mask=0;mask<1<<edges.length;mask++){
  const a=parts(Q*S,edges,mask).map(v=>v.length),hi=a.filter(x=>x>H),lo=a.filter(x=>x<=H);
  add(U,polyKey(hi,lo));
 }
 const Fs=blocks.map(bloc), cuts=Array.from({length:1<<core.length},(_,i)=>parts(Q,core,i));
 let count=0,support=0;
 function seek(r,d=[]) {
  if(d.length<r.length){for(let i=0;i<=D;i++)seek(r,[...d,i]);return;}
  const high=r.map((x,i)=>S*x-d[i]), Hkey=key(high)+'|', mul=new Map();
  high.forEach(x=>add(mul,x));
  let f=1;for(const m of mul.values())for(let j=2;j<=m;j++)f*=j;
  const A=new Map([...U].filter(([k])=>k.startsWith(Hkey)).map(([k,v])=>[k.slice(Hkey.length),f*v])),B=new Map();
  for(const cut of cuts)for(const L of labeled(cut,r)){
   let C=new Map([['',1]]);
   L.forEach((v,i)=>{C=join(C,cutProduct(v,Fs,d[i]));});
   for(const [k,c] of C)add(B,k,c);
  }
  if(!equal(A,B))throw Error(JSON.stringify({r,d,A:[...A],B:[...B]}));count++;support+=A.size;
 }
 for(const r of [[3],[1,2],[1,1,1]])seek(r);
 return {queries:count,nonzeroCoefficients:support};
}
const star=[[0,1],[0,2],[0,3],[0,4],[0,5]];
const endpointBranch=[[0,1],[1,2],[2,3],[0,4],[0,5]];
const centeredBranch=[[0,1],[1,2],[1,3],[0,4],[0,5]];
console.log(JSON.stringify([check([endpointBranch,centeredBranch,endpointBranch]),check([star,endpointBranch,endpointBranch])]));
