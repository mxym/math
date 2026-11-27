const p=17,m=x=>(x%17+17)%17,R=Array.from({length:17},(_,i)=>i),iv=R.map(x=>R.find(y=>m(x*y)===1)),N=289;
const dif=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>{let x=m(i%17-j%17),y=m((i/17|0)-(j/17|0));return [x,y,x?m(y*iv[x]):17];}));
for(let [name,Q] of [['rank1',(x,y)=>x*x],['split',(x,y)=>x*y],['nonsplit',(x,y)=>x*x-3*y*y]]){let cases=0,nodes=0,count=0,ex=null,hist={};for(let s=0;s<18;s++)for(let t=s+1;t<18;t++){
const good=([x,y,d])=>d===s||d===t||m(Q(x,y))===1;
const C=[0];
function go(h){nodes++;if(C.length===6){count++;let K=[s,t,new Set(C.map(a=>a%17)).size];hist[K]=(hist[K]||0)+1;ex??={s,t,C:C.slice()};return;}
 for(let i=0;i<h.length;i++){let a=h[i],hs=Array(18).fill(0);let ok=C.every(b=>++hs[dif[a][b][2]]<=2);if(!ok)continue;
 let u=h.slice(i+1).filter(b=>good(dif[a][b]));if(C.length+1+u.length<6)continue;
 C.push(a);go(u);C.pop();
 }}
 const h=Array.from({length:N-1},(_,i)=>i+1).filter(a=>good(dif[0][a]));go(h);
}if(name==="rank1"){if(count!==2774400||nodes!==3801341||Object.keys(hist).some(k=>{let [s,t,r]=k.split(",").map(Number);return t!==17||r!==2;}))throw Error("rank-one exceptions");}else if(count||nodes!==(name==="split"?28878:29753))throw Error("binary conic exception");console.log({name,nodes,count});}

let tests=0;
function sums(y,a){let u=iv[m(y)],r=m(a*u);return [m(13*r*r+10*u*u),m(-(r**3)+13*r*u*u)];}
for(let t=2;t<17;t++)for(let a of R)for(let b of R){
 ++tests;
 const A=String(sums(1,a)),B=String(sums(t,b)),C=String(sums(t-1,b-a));
 if(A===B&&A===C)throw Error("three-level cubic sums");
}
console.log({tests});

const set=(X,Y)=>[...new Set(X.flatMap(a=>Y.map(b=>m(a-b))))].sort((a,b)=>a-b);
const universe=[];for(let a=0;a<17;a++)for(let b=a+1;b<17;b++)for(let c=b+1;c<17;c++)if(m(a+b+c)===0)universe.push([a,b,c]);
const idx=new Set(),parts=[];
for(let i=0;i<universe.length;i++)if(!idx.has(i)){let s=[i];idx.add(i);
 for(let j of s)for(let k=0;k<universe.length;k++)if(!idx.has(k)&&set(universe[j],universe[k]).length<=6){idx.add(k);s.push(k);}
 parts.push(s.map(j=>universe[j]));
}
const rep=[[0,1,16],[4,6,7],[10,11,13]],map=(S,a)=>S.map(x=>m(a*x)).sort((i,j)=>i-j).join();
if(universe.length!==40||parts.filter(s=>s.length===2).length!==8||parts.filter(s=>s.length===3).length!==8)throw Error("near-Cauchy-Davenport");
for(let s of parts){
 if(s.length===2){
  if(s.some(x=>set(x,x).length<=6)||set(s[0],s[1]).length!==6)throw Error("mirror component");
 }else{
  const a=R.slice(1).find(a=>rep.every(x=>s.some(y=>map(x,a)===y.join())));
  if(!a)throw Error("active component");
  if(s.filter(x=>set(x,x).length<=6).length!==1||s.some(x=>s.some(y=>x!==y&&set(x,y).length!==6)))throw Error("component edges");
 }
}
const diffsets=rep.flatMap(x=>rep.map(y=>set(x,y))).filter(x=>x.length<=6);
for(let X of diffsets)for(let Y of diffsets)for(let a=2;a<16;a++)for(let b of R){let Z=new Set(X.concat(Y.map(x=>m(a*x+b))));if(Z.size<=6)throw Error("unequal parallel chord widths");}
function mean(X){return m(X.reduce((s,x)=>s+x,0)*iv[X.length]);}
function e2(X){let z=mean(X);return m(-iv[2]*X.reduce((s,x)=>s+(x-z)**2,0));}
const means=[mean(set(rep[0],rep[1])),mean(set(rep[0],rep[2])),mean(set(rep[1],rep[2]))];
const coeffs=[e2(set(rep[0],rep[0])),e2(set(rep[0],rep[1])),e2(set(rep[0],rep[2]))];
if(String(means)!=="3,14,0"||String(coeffs)!=="12,4,4")throw Error("near AP centroid constants");
console.log({centeredTriples:universe.length,components:parts.length,means,coeffs});
