'use strict';
// Exact fixed-dyadic Gaussian disk cover for two real-sextic parameter domains.
// The floating-point sqrt supplies a seed only; integer square comparisons certify the interval.
const SCALE = 131072;
const MAX = Number(process.argv[2] || Infinity);
const shard = process.argv[3] === undefined ? -1 : Number(process.argv[3]);
const SHARDS=2;
if (!Number.isInteger(shard)||shard<0||shard>=SHARDS) throw new Error('invalid shard');
const nil = [0, 0, 0, 0, 0], one = [SCALE, 0, 0, SCALE, SCALE];

function tx(n) { if (!Number.isSafeInteger(n)) throw new Error("unsafe integer " + n); return n; }
function sqfloor(q) {
  const g = Math.floor(Math.sqrt(q));
  if (!Number.isSafeInteger(g) || g < 0) throw new Error("noninteger sqrt seed");
  if (g < 67108864 && g*g <= q && (g+1)*(g+1) > q) return g;
  // The seed is not used as evidence in either branch.
  let l=0,h=67108864;
  while (h-l>1) {const m=(l+h)>>1;if (m*m<=q) l=m; else h=m;}
  return l;
}
function normBounds(x, y) {
  x=Math.abs(x); y=Math.abs(y);
  let d=1;
  while (x/d > 33554432 || y/d > 33554432) d*=2;
  const a=Math.floor(x/d), b=Math.floor(y/d), aa=Math.ceil(x/d),bb=Math.ceil(y/d);
  const q=a*a+b*b, r=aa*aa+bb*bb;
  const lo=sqfloor(q), hi=r===q?lo:sqfloor(r);
  return [d*lo,d*(hi+(hi*hi<r?1:0))];
}
function make(x,y,r) {
  const [lo,hi]=normBounds(x,y);
  return [x,y,r,hi,lo];
}
function add(a,b) {if(a===nil)return b;if(b===nil)return a;return make(tx(a[0]+b[0]),tx(a[1]+b[1]),tx(a[2]+b[2]));}
function scale(a,n) {
  const z=Math.abs(n);
  return [tx(a[0]*n),tx(a[1]*n),tx(a[2]*z),tx(a[3]*z),tx(a[4]*z)];
}
function mul(a,b) {
  if(a===nil||b===nil)return nil;if(a===one)return b;if(b===one)return a;
  const px = tx(tx(a[0]*b[0])-tx(a[1]*b[1])), py = tx(tx(a[0]*b[1])+tx(a[1]*b[0]));
  const x = Math.trunc(px/SCALE), y = Math.trunc(py/SCALE);
  const err = (x*SCALE===px?0:1)+(y*SCALE===py?0:1);
  const num=tx(tx(a[2]*(b[3]+b[2]))+tx(b[2]*a[3]));
  return make(x,y,Math.ceil(num/SCALE)+err);
}
function truncDiv(n,d) {
  const x=Math.trunc(n/d), a=tx(x*d);
  if(n>=0?(a<=n&&tx(a+d)>n):(a>=n&&tx(a-d)<n)) return x;
  // The only use is with exact small positive divisors; fail loudly otherwise.
  throw new Error("uncertified division");
}

const lo=new Array(5), hi=new Array(5), losq=new Array(5), hisq=new Array(5);
const lo4=new Array(5),hi4=new Array(5),w=new Array(5);
lo[0]=hi[0]=losq[0]=hisq[0]=lo4[0]=hi4[0]=SCALE;w[0]=one;
const mid = (x,y)=>Math.floor((x+y)/2);
function dist(a,b) {return a>0?a:b<0?-b:0;}
function elem(skip) {
  const groups=[[[0],[1],[2],[3,4]],[[0,1],[2],[3],[4]]][shard];
  const realDisk=(L,U)=>{const c=mid(L,U);return make(c,0,U-c);};
  let poly=[one];
  for(const ids of groups){
    const g=ids.filter(i=>i!==skip);
    if(!g.length)continue;
    const h=g.length===2?[one,realDisk(2*rxlo[g[0]],2*rxhi[g[0]]),realDisk(losq[g[0]],hisq[g[0]])]:[one,w[g[0]]];
    const newPoly=Array(poly.length+h.length-1).fill(nil);
    for(let i=0;i<poly.length;i++)for(let j=0;j<h.length;j++)newPoly[i+j]=add(newPoly[i+j],mul(poly[i],h[j]));
    poly=newPoly;
  }
  return poly;
}
function G(j) {
  const e=elem(j),c=w[j];
  return add(mul(c,add(mul(c,add(mul(c,add(scale(c,30),scale(e[1],-10))),scale(e[2],5))),scale(e[3],-3))),scale(e[4],2));
}
const P = SCALE,rxlo=new Array(5),rxhi=new Array(5);
function negconj(a){return [a[0],-a[1],a[2],a[3],a[4]];}
function setnorm(index, z, q, Q) {
  if(q>P*P)return false;
  Q=Math.min(Q,P*P);
  const n=sqfloor(Q);
  w[index]=z;lo[index]=sqfloor(q);hi[index]=n+(n*n<Q?1:0);
  losq[index]=Math.floor(q/P);hisq[index]=Math.ceil(Q/P);
  lo4[index]=Math.floor(losq[index]*losq[index]/P);hi4[index]=Math.ceil(hisq[index]*hisq[index]/P);
  return true;
}
function real(a,q,id){
  const x=mid(a[q],a[q+4]), R=a[q+4]-x,min=dist(a[q],a[q+4]),
        max=Math.max(Math.abs(a[q]),Math.abs(a[q+4]));
  rxlo[id]=a[q];rxhi[id]=a[q+4];
  return setnorm(id,make(x,0,R),min*min,max*max);
}
function comp(a,q,k,id1,id2){
  const x=mid(a[q],a[q+4]),y=mid(a[k],a[k+4]),x0=dist(a[q],a[q+4]),y0=dist(a[k],a[k+4]);
  const dx=a[q+4]-x,dy=a[k+4]-y,r2=dx*dx+dy*dy,t=sqfloor(r2);
  const r=t+(t*t<r2?1:0),x1=Math.max(Math.abs(a[q]),Math.abs(a[q+4])),
        y1=Math.max(Math.abs(a[k]),Math.abs(a[k+4]));
  const z=make(x,y,r),L=x0*x0+y0*y0,U=x1*x1+y1*y1;
  rxlo[id1]=rxlo[id2]=a[q];rxhi[id1]=rxhi[id2]=a[q+4];
  return setnorm(id1,z,L,U)&&setnorm(id2,negconj(z),L,U);
}
function arc(a,q,id1,id2){
  const t=mid(a[q],a[q+4]), d=P*P+t*t;
  const x=truncDiv((P*P-t*t)*P,d), y=truncDiv((2*P*t)*P,d);
  const r=2*(a[q+4]-t)+2;
  const z=make(x,y,r);
  const lo=a[q],hi=a[q+4],D0=P*P+hi*hi,D1=P*P+lo*lo;
  rxlo[id1]=rxlo[id2]=truncDiv((P*P-hi*hi)*P,D0);
  rxhi[id1]=rxhi[id2]=truncDiv((P*P-lo*lo)*P,D1)+1;
  return setnorm(id1,z,P*P,P*P)&&setnorm(id2,negconj(z),P*P,P*P);
}
function makeBox(a){
  rxlo[0]=rxhi[0]=P;
  if(shard===0)
    return a[0]<=a[5]&&setnorm(0,one,P*P,P*P)&&real(a,0,1)&&real(a,1,2)&&comp(a,2,3,3,4);
  if(shard===1)
    return a[0]<=a[5]&&a[1]<=a[6]&&arc(a,3,0,1)&&real(a,0,2)&&real(a,1,3)&&real(a,2,4);
  throw Error('unexpected shard');
}
const distinct=[[0,1,2,3],[0,2,3,4]];
function evalbox(a){
  if(!makeBox(a))return 1;
  // This stronger threshold does not use the 5/6-only local or product cuts.
  for(const j of distinct[shard]){
    const g=G(j), u=g[3]+g[2], d=lo4[j];
    if(d&&5*u<243*d)return 2;
  }
  return 0;
}
function verifyWitness() {
  const A=([x,y],[s,t])=>[x+s,y+t];
  const B=([x,y],[s,t])=>[x*s-y*t,x*t+y*s];
  const C=([x,y],s)=>[x*s,y*s];
  const D=([x,y])=>x*x+y*y;
  const M=1000000n;
  const W=[[M,0n],[-940749n,0n],[-87397n,0n],[16905n,974002n],[16905n,-974002n]];
  for(let j=0;j<5;j++){
    const e=[[1n,0n],[0n,0n],[0n,0n],[0n,0n],[0n,0n]];
    for(let i=0;i<5;i++)if(j!==i)
      for(let k=4;k>=1;k--)e[k]=A(e[k],B(e[k-1],W[i]));
    let g=[30n,0n];
    for(let k=1;k<=4;k++)g=A(B(g,W[j]),C(e[k],[-10n,5n,-3n,2n][k-1]));
    if(M*M*D(g)<=(60n*800003n)**2n*D(W[j])**4n)throw Error("witness inequality "+j);
  }
  console.log("All five exact witness inequalities exceed 800003/1000000");
}
verifyWitness();
const initial=[-P,-P,-P,0,P,P,P,P];
const stack=[[initial,0]],cuts=[0,0];
let nodes=0,maxDepth=0,start=Date.now();
while(stack.length&&nodes<MAX){
  const [a,d]=stack.pop();
  nodes++;maxDepth=Math.max(d,maxDepth);
  const cut=evalbox(a);
  if(cut){cuts[cut-1]++;continue;}
  if(nodes%1000000===0)console.log('progress',{shard,nodes,maxDepth,cuts,corner:a.slice(0,4),sec:(Date.now()-start)/1000});
  let k=0,w=0;
  for(let i=0;i<4;i++){const h=a[i+4]-a[i];if(h>w){w=h;k=i;}}
  if(w<2)throw Error("unresolved box "+JSON.stringify(a));
  const b=a.slice(),v=mid(a[k],a[k+4]);b[k]=a[k+4]=v;
  stack.push([a,d+1],[b,d+1]);
}
console.log(stack.length?'PARTIAL':'PASS',{shard,nodes,maxDepth,cuts,pending:stack.length,sec:(Date.now()-start)/1000});
