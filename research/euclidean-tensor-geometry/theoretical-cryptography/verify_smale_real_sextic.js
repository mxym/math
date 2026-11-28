'use strict';
// Exact fixed-dyadic Gaussian disk cover for the sextic objective.
// The floating-point sqrt supplies a seed only; integer square comparisons certify the interval.
const LOW = 131072, HIGH = 1048576;
let SCALE = LOW;
const MAX = Number(process.argv[2] || Infinity);
const shard = process.argv[3] === undefined ? -1 : Number(process.argv[3]);
const SHARDS=4;
if (!Number.isInteger(shard)||shard<0||shard>=SHARDS) throw new Error('invalid shard');
const resTerms = [[[5,0,0,0],1,48,3125],[[4,1,0,1],2,-144,15625],[[4,0,2,0],2,-18,3125],[[4,0,1,2],3,486,78125],[[4,0,0,4],4,-2187,1953125],[[3,2,1,0],2,18,3125],[[3,2,0,2],3,-18,78125],[[3,1,2,1],3,-9,3125],[[3,1,1,3],4,243,390625],[[3,1,0,0],1,-16,125],[[3,0,4,0],3,27,50000],[[3,0,3,2],4,-81,625000],[[3,0,1,1],2,36,3125],[[3,0,0,3],3,-972,390625],[[2,4,0,0],2,-3,3125],[[2,3,1,1],3,9,15625],[[2,3,0,3],4,-48,390625],[[2,2,3,0],3,-3,25000],[[2,2,2,2],4,9,312500],[[2,2,0,1],2,204,3125],[[2,1,2,0],2,21,625],[[2,1,1,2],3,-3357,78125],[[2,1,0,4],4,15552,1953125],[[2,0,3,1],3,81,62500],[[2,0,2,3],4,-243,781250],[[2,0,1,0],1,6,25],[[2,0,0,2],2,-18,3125],[[1,3,1,0],2,-21,625],[[1,3,0,2],3,96,78125],[[1,2,2,1],3,267,15625],[[1,2,1,3],4,-288,78125],[[1,2,0,0],1,6,25],[[1,1,4,0],3,-81,25000],[[1,1,3,2],4,243,312500],[[1,1,1,1],2,-123,625],[[1,1,0,3],3,1152,78125],[[1,0,3,0],2,-81,1000],[[1,0,2,2],3,1377,15625],[[1,0,1,4],4,-31104,1953125],[[1,0,0,1],1,-12,25],[[0,5,0,0],2,16,3125],[[0,4,1,1],3,-48,15625],[[0,4,0,3],4,256,390625],[[0,3,3,0],3,2,3125],[[0,3,2,2],4,-12,78125],[[0,3,0,1],2,-48,625],[[0,2,2,0],2,33,500],[[0,2,1,2],3,672,15625],[[0,2,0,4],4,-18432,1953125],[[0,1,3,1],3,-567,12500],[[0,1,2,3],4,3888,390625],[[0,1,1,0],1,-3,5],[[0,1,0,2],2,192,625],[[0,0,5,0],3,729,100000],[[0,0,4,2],4,-2187,1250000],[[0,0,2,1],2,81,250],[[0,0,1,3],3,-3456,15625],[[0,0,0,5],4,331776,9765625]];
const nil = [0, 0, 0, 0, 0];
let one = [SCALE, 0, 0, SCALE, SCALE];

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
function scaleFrac(a,n,d) {
  const px=tx(a[0]*n),py=tx(a[1]*n),x=truncDiv(px,d),y=truncDiv(py,d);
  const err=(x*d===px?0:1)+(y*d===py?0:1);
  const v=tx(a[2]*Math.abs(n)), q=truncDiv(v,d);
  return make(x,y,q+(q*d===v?0:1)+err);
}

const lo=new Array(5), hi=new Array(5), losq=new Array(5), hisq=new Array(5);
const lo4=new Array(5),hi4=new Array(5),w=new Array(5);
lo[0]=hi[0]=losq[0]=hisq[0]=lo4[0]=hi4[0]=SCALE;w[0]=one;
const mid = (x,y)=>Math.floor((x+y)/2);
function dist(a,b) {return a>0?a:b<0?-b:0;}
function elem(skip) {
  const groups=[[[0],[1],[2],[3,4]],[[0,1],[2],[3],[4]],[[0],[1,2],[3,4]],[[0,1],[2,3],[4]]][shard];
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
function anchorAMGM(a) {
  const M=2*SCALE,A=a[0]+a[2],B=a[4]+a[6],C=hisq[1]+hisq[2],D=hisq[3]+hisq[4];
  const N=30*M*M-20*(A+B)*M+5*(C+D)*M+20*A*B-6*(A*D+B*C)+2*C*D;
  return N<50*M*M;
}
function algebraicCuts() {
  if(Math.min(...lo)*5<=4*SCALE) return 0; // guard only
  const e=elem(-1);
  let lp=SCALE,U=0;
  for(let j=1;j<5;j++){
    lp=Math.floor(lp*lo[j]/SCALE); U+=e[j][3]+e[j][2];
  }
  if(lp>0 && 7*U<=lp)return 5;
  // Certified quadratic signed-product shortcut.
  if(lp>0 && 4*U<=lp){
    const n=e.slice(1,5).map(z=>z[3]+z[2]);
    const N=400*n[0]*n[0]+100*n[1]*n[1]+25*n[2]*n[2]+4*n[3]*n[3];
    if(N<=25*lp*lp){
      const z=e[5], conj=[z[0],-z[1],z[2],z[3],z[4]];
      const cross=mul(add(scale(mul(e[1],e[4]),12),scale(mul(e[2],e[3]),15)),conj);
      if(10*SCALE*(cross[0]-cross[2])>N)return 6;
    }
  }
  if(!(2*U<lp&&e[5][3]+e[5][2]<=2*SCALE))return 0;
  const pow=Array.from({length:5},(_,j)=>{
    const p=[one];for(let k=1;k<=(j===4?4:8);k++)p.push(mul(p[k-1],e[j+1]));
    return p;
  });
  let Q=nil;
  for(const [alpha,k,n,d] of resTerms){
    let v=pow[4][4-k];
    for(let j=0;j<4;j++)if(alpha[j])v=mul(v,pow[j][alpha[j]]);
    Q=add(Q,scaleFrac(v,n,d));
  }
  const D=pow[4][4],UQ=Q[3]+Q[2];
  const cross=mul([D[0],-D[1],D[2],D[3],D[4]],Q);
  if(tx(tx(2*SCALE*(cross[0]+cross[2]))+tx(UQ*UQ))<0)return 6;
  return 0;
}

let P = SCALE;
const rxlo=new Array(5),rxhi=new Array(5);
function setScale(s){if(s!==P){P=SCALE=s;one=make(s,0,0);}}
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
function truncProdDiv(x,y,d){
 const n=x*y;if(Number.isSafeInteger(n))return truncDiv(n,d);
 return tx(Number((BigInt(x)*BigInt(y))/BigInt(d)));
}
function arc(a,q,id1,id2){
  const t=mid(a[q],a[q+4]), d=P*P+t*t;
  const x=truncProdDiv(P*P-t*t,P,d), y=truncProdDiv(2*P*t,P,d);
  const r=2*(a[q+4]-t)+2;
  const z=make(x,y,r);
  const lo=a[q],hi=a[q+4],D0=P*P+hi*hi,D1=P*P+lo*lo;
  rxlo[id1]=rxlo[id2]=truncProdDiv(P*P-hi*hi,P,D0);
  rxhi[id1]=rxhi[id2]=truncProdDiv(P*P-lo*lo,P,D1)+1;
  return setnorm(id1,z,P*P,P*P)&&setnorm(id2,negconj(z),P*P,P*P);
}
function makeBox(a){
  rxlo[0]=rxhi[0]=P;
  if(shard===0)
    return a[0]<=a[5]&&setnorm(0,one,P*P,P*P)&&real(a,0,1)&&real(a,1,2)&&comp(a,2,3,3,4);
  if(shard===1)
    return a[0]<=a[5]&&a[1]<=a[6]&&arc(a,3,0,1)&&real(a,0,2)&&real(a,1,3)&&real(a,2,4);
  if(shard===2)
    return a[0]<=a[6]&&setnorm(0,one,P*P,P*P)&&comp(a,0,1,1,2)&&comp(a,2,3,3,4);
  if(shard===3)
    return arc(a,0,0,1)&&comp(a,1,2,2,3)&&real(a,3,4);
  throw Error('unexpected shard');
}
const distinct=[ [0,1,2,3], [0,2,3,4], [0,1,3], [0,2,4] ];
function evalbox(a){
  if(!makeBox(a))return 1;
  const ac=algebraicCuts();if(ac)return ac===5?3:4;
  for(const j of distinct[shard]){
    const g=G(j), u=g[3]+g[2], d=lo4[j];
    if(d&&u<50*d)return 2;
  }
  return 0;
}
const initial=[[-P,-P,-P,0],[-P,-P,-P,0],[-P,0,-P,0],[0,-P,0,-P]][shard].concat([P,P,P,P]);
const stack=[[initial,0,LOW]],cuts=[0,0,0,0];
let promoted=0;
let nodes=0,maxDepth=0,start=Date.now();
while(stack.length&&nodes<MAX){
  const [a,d,sc]=stack.pop();
  setScale(sc);
  nodes++;maxDepth=Math.max(d,maxDepth);
  const cut=evalbox(a);
  if(cut){cuts[cut-1]++;continue;}
  if(nodes%1000000===0)console.log('progress',{shard,nodes,maxDepth,cuts,corner:a.slice(0,4),sec:(Date.now()-start)/1000});
  let k=0,w=0;
  for(let i=0;i<4;i++){const h=a[i+4]-a[i];if(h>w){w=h;k=i;}}
  if(w<4&&sc===LOW){promoted++;stack.push([a.map(x=>x*(HIGH/LOW)),d,HIGH]);continue;}
  if(w<2)throw Error("unresolved box "+JSON.stringify({a,sc}));
  const b=a.slice(),v=mid(a[k],a[k+4]);b[k]=a[k+4]=v;
  stack.push([a,d+1,sc],[b,d+1,sc]);
}
console.log(stack.length?'PARTIAL':'PASS',{shard,nodes,maxDepth,cuts,pending:stack.length,promoted,sec:(Date.now()-start)/1000});
