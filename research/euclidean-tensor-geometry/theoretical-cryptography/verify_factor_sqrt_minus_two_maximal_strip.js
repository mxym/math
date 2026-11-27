"use strict";
// Exact reconstruction of the four maximal Q-periodic components, then
// two independent projected norm checks for the first possible real-part strip.
const assert=require("node:assert/strict");
const BASE=1122,T=197,PS=[19,5,41,43,59,67];
const mod=(a,p)=>((a%p)+p)%p;
const step=[];
for(let a=-2;a<=2;++a)for(let b=-1;b<=1;++b)if(a||b)step.push([a,b]);
const small=[2,3,11,17];
function parents() {
  const Q=BASE,W=Q*Q;
  const allow=new Uint8Array(W), seen=new Int32Array(W), xa=new Int32Array(W),xb=new Int32Array(W);
  for(let a=0;a<Q;++a)for(let b=0;b<Q;++b) {
    const n=a*a+2*b*b;
    if(small.every(p=>n%p!==0))allow[a*Q+b]=1;
  }
  let total=0,n=0,mx=0;
  const C=[];
  for(let a=0;a<Q;++a)for(let b=0;b<Q;++b){
    const s=a*Q+b;
    if(!allow[s]||seen[s])continue;
    ++n;seen[s]=n;xa[s]=a;xb[s]=b;const q=[s];
    for(let i=0;i<q.length;++i){
      const u=q[i],x=xa[u],y=xb[u];
      for(const [da,db] of step){
        const A=x+da,B=y+db,t=mod(A,Q)*Q+mod(B,Q);
        if(!allow[t])continue;
        if(seen[t]) {
          assert.equal(n,seen[t]);assert.equal(A,xa[t]);assert.equal(B,xb[t]);
        } else {
          seen[t]=n;xa[t]=A;xb[t]=B;q.push(t);
        }
      }
    }
    total+=q.length;mx=Math.max(mx,q.length);
    if(q.length>=T)C.push(q.map(i=>[xa[i],xb[i]]));
  }
  return {count:n,allowed:total,mx,C};
}
function build(P) {
  const J=PS.length,sc=Array(J).fill(0),kc=Array(J).fill(0),mx=Array(J).fill(0),sol=[];
  for(const C of P.C) {
    const N=C.length, by=new Map(C.map(([a,b],i)=>[a+","+b,i]));
    const adj=C.map(([a,b])=>step.map(([da,db])=>by.get((a+da)+","+(b+db))).filter(i=>i!==undefined));
    function advance(S,j,Q,oa,ob) {
      if(j===J) {
        assert.equal(S.length,T);
        let anchor=S.map(i=>C[i]).sort((x,y)=>x[0]-y[0]||x[1]-y[1])[0];
        const shape=S.map(i=>[C[i][0]-anchor[0],C[i][1]-anchor[1]]);
        shape.sort((x,y)=>x[0]-y[0]||x[1]-y[1]);
        sol.push({a:mod(anchor[0]+oa,Q),b:mod(anchor[1]+ob,Q),shape});
        return;
      }
      const p=PS[j],slope=Q%p;
      const ra=C.map(z=>mod(z[0]+oa,p)), rb=C.map(z=>mod(z[1]+ob,p));
      const mark=new Uint8Array(N);
      const sq=Array.from({length:2*p},(_,a)=>a*a%p);
      for(let a=0;a<p;++a)for(let b=0;b<p;++b) {
        ++sc[j];
        const x=slope*a%p,y=slope*b%p;
        for(const u of S)mark[u]=((sq[ra[u]+x]+2*sq[rb[u]+y])%p)?1:0;
        for(const s of S) if(mark[s]) {
          mark[s]=0;const queue=[s];
          for(let i=0;i<queue.length;++i) for(const v of adj[queue[i]]) if(mark[v]) {
            mark[v]=0;queue.push(v);
          }
          mx[j]=Math.max(mx[j],queue.length);
          if(queue.length>=T){++kc[j];advance(queue,j+1,Q*p,oa+Q*a,ob+Q*b);}
        }
      }
    }
    advance(C.map((_,i)=>i),0,BASE,0,0);
  }
  return {sol,sc,kc,mx};
}
function orbit(s) {
  const a=[];
  for(const x of [-1,1])for(const y of [-1,1]) {
    const r=s.map(([u,v])=>[x*u,y*v]).sort((t,w)=>t[0]-w[0]||t[1]-w[1]);
    const [A,B]=r[0];
    a.push(JSON.stringify(r.map(([u,v])=>[u-A,v-B])));
  }
  return a.sort()[0];
}
function prime(p){
  if(p<2)return false;
  for(let d=2;d*d<=p;++d)if(p%d===0)return false;
  return true;
}

const P=parents();
assert.equal(P.count,6688);assert.equal(P.allowed,204800);
assert.equal(P.mx,2283);assert.equal(P.C.length,206);
const R=build(P);
const Q=PS.reduce((a,p)=>a*p,BASE);
assert.equal(Q,742840526010);
assert.deepEqual(R.sc,[74366,3500,20172,81356,69620,53868]);
assert.deepEqual(R.kc,[140,12,44,20,12,4]);
assert.deepEqual(R.mx,[298,241,217,205,201,197]);
const ordered=R.sol.sort((x,y)=>x.a-y.a||x.b-y.b);
assert.deepEqual(ordered.map(({a,b})=>[a,b]),[
 [287186037979,371420262993],[287186037979,742840525998],
 [455654487987,371420262976],[455654487987,742840525981],
]);
assert.equal(new Set(ordered.map(s=>orbit(s.shape))).size,1);
const pattern=ordered[1], reflected=ordered[3];
const sort=(a)=>a.sort((x,y)=>x[0]-y[0]||x[1]-y[1]);
assert.deepEqual(pattern.shape,ordered[0].shape);
assert.deepEqual(reflected.shape,ordered[2].shape);
assert.equal(ordered[1].b-ordered[0].b,Q/2);
assert.equal(ordered[3].b-ordered[2].b,Q/2);
const refl=sort(pattern.shape.map(([x,y])=>[-(pattern.a+x),pattern.b+y]));
assert.equal(mod(refl[0][0],Q),reflected.a);assert.equal(mod(refl[0][1],Q),reflected.b);
assert.deepEqual(refl.map(([x,y])=>[x-refl[0][0],y-refl[0][1]]),reflected.shape);
const span=Math.max(...pattern.shape.map(z=>z[0]));
assert.equal(span,44);
assert.ok(pattern.a+span<Q/2);
const primesOld=[...small,...PS];
assert.equal(primesOld.reduce((a,p)=>a*p,1),Q);
for(const p of primesOld)assert.ok(prime(p));
function primeNormRepresentations(p) {
 const out=[];
 for(let a=0;a*a<=p;++a)for(let b=0;a*a+2*b*b<=p;++b)
   if(a*a+2*b*b===p)out.push([a,b]);
 return out;
}
function irreducible(a,b) {
 return prime(a*a+2*b*b) ||
   (b===0 && prime(Math.abs(a)) && !primeNormRepresentations(Math.abs(a)).length);
}
const exceptionSet=new Set();
for(const p of primesOld) {
 const reps=primeNormRepresentations(p);
 if(!reps.length){exceptionSet.add(p+",0");exceptionSet.add(-p+",0");}
 else for(const [a,b] of reps)for(const e of [-1,1])for(const f of [-1,1])
   exceptionSet.add((e*a)+","+(f*b));
}
// Direct finite closure in the actual irreducible-only graph near the origin.
const C90=[[0,1]], used=new Set(["0,1"]);
for(let i=0;i<C90.length;++i) {
 const [a,b]=C90[i];
 for(const [da,db] of step) {
   const x=a+da,y=b+db,z=x+","+y;
   if(!used.has(z)&&irreducible(x,y)) {
     used.add(z);C90.push([x,y]);
     assert.ok(C90.length<=90);
   }
 }
}
assert.equal(C90.length,90);
for(const z of exceptionSet)assert.ok(used.has(z));

function sift(x,y) {
 return primesOld.every(p=>{const a=mod(x,p),b=mod(y,p);return (a*a+2*b*b)%p!==0;});
}
for(const {a,b,shape} of ordered) {
 const S=new Set(shape.map(z=>z.join(",")));
 assert.equal(S.size,197);
 for(const [u,v] of shape) {
   assert.ok(sift(a+u,b+v));
   for(const [du,dv] of step)if(!S.has((u+du)+","+(v+dv)))
      assert.ok(!sift(a+u+du,b+v+dv));
 }
}

function project(shape,p) {
 const pairs=shape.map(([u,v])=>[mod(u,p),mod(v,p)]), row=new Uint8Array(p);
 const first=new Int16Array(p).fill(-1);
 for(let a=0;a<p;++a)for(let b=0;b<p;++b)if(pairs.every(([u,v])=>((u+a)*(u+a)+2*(v+b)*(v+b))%p!==0)){
   row[a]=1;first[a]=b;break;
 }
 // Independently enumerate the excluded y values by splitting x^2+2y^2.
 const roots=Array.from({length:p},(_,r)=>r).filter(r=>(r*r+2)%p===0);
 const inverses=roots.map(r=>{
   for(let s=1;s<p;++s)if(r*s%p===1)return s;
   throw Error("bad root inverse");
 });
 assert.ok(inverses.length===0||inverses.length===2);
 const forbidden=new Uint8Array(p);
 for(let a=0;a<p;++a) {
   forbidden.fill(0);
   for(const [u,v] of pairs) {
     const x=(a+u)%p;
     if(!inverses.length) {
       if(!x)forbidden[mod(-v,p)]=1;
     } else for(const r of inverses)forbidden[mod(x*r-v,p)]=1;
   }
   assert.equal(forbidden.indexOf(0),first[a]);
 }
 return {row,first,n:row.reduce((a,b)=>a+b,0)};
}
const localRows=[];
for(let p=2;p<=394;++p)if(prime(p)&&Q%p!==0) {
 const row=project(pattern.shape,p);
 assert.ok(row.n);
 localRows.push({p,...row});
}
const thin=localRows.filter(z=>z.n<z.p);
assert.deepEqual(thin.map(z=>[z.p,z.n]),[
 [7,1],[73,1],[83,6],[89,24],[97,36],[107,39],
 [113,75],[131,113],[137,120],[139,125],[179,178],
]);
const q=BigInt(Q), a0=BigInt(pattern.a);
const modBig=(z,p)=>Number((z%BigInt(p)+BigInt(p))%BigInt(p));
const rowAt=(k,p)=>(pattern.a%p+(Q%p)*mod(k,p))%p;
const pass=k=>thin.every(({p,row})=>row[rowAt(k,p)]);
let firstK=null, checked=0;
for(let m=0;m<=507627&&firstK===null;++m)for(const k of m?[-m,m]:[0]) {
 ++checked;
 if(pass(k)){firstK=k;break;}
}
assert.equal(firstK,-507627);assert.equal(checked,1015254);
const A=a0+q*BigInt(firstK);
const H=A>0n?A:-A-BigInt(span);
assert.equal(A,-377085620510840291n);
assert.equal(H,377085620510840247n);

// Independent search using the two singleton projections and exact BigInt remainders.
const base511=[];
for(let r=0;r<511;++r)
 if(thin.slice(0,2).every(({p,row})=>row[modBig(a0+q*BigInt(r),p)]))base511.push(r);
assert.equal(base511.length,1);
const [r0]=base511;
let near=null, nearK=null;
for(let k=-507627+mod(r0+507627,511);k<=507627;k+=511) {
 const x=a0+q*BigInt(k), d=x>0n?x:-x-BigInt(span);
 if(localRows.every(({p,first})=>first[modBig(x,p)]>=0)&&(near===null||d<near)) {
   near=d;nearK=k;
 }
}
assert.equal(near,H);assert.equal(nearK,firstK);
assert.ok(q*507628n-a0-BigInt(span)>H);

// Exhibit a literal CRT y-progression at the first feasible x-coordinate.
let bound=BigInt(pattern.b), M=q;
for(const {p,first} of localRows) {
  const b=first[modBig(A,p)];
  assert.ok(b>=0);
  const j=Array.from({length:p},(_,j)=>j)
    .find(j=>modBig(bound+BigInt(j)*M,p)===b);
  assert.ok(j!==undefined);
  bound+=BigInt(j)*M;M*=BigInt(p);
}
const term=([u,v])=>[A+BigInt(u),bound+BigInt(v)];
const values=pattern.shape.map(term);
for(let p=2;p<=394;++p)if(prime(p)) {
 assert.equal(modBig(M,p),0);
 for(const [a,b] of values)assert.notEqual(modBig(a*a+2n*b*b,p),0);
}
const numerator=thin.reduce((a,x)=>a*BigInt(x.n),1n);
const denominator=thin.reduce((a,x)=>a*BigInt(x.p),1n);
console.log(JSON.stringify({
 parentComponents:P.count,parentAllowed:P.allowed,retained:R.kc,shifts:R.sc,
 originComponent:C90.length,primeExceptions:exceptionSet.size,
 period:Q,maximalClasses:ordered.map(({a,b})=>[a,b]),
 orbitCount:1,width:span,singletonCRT:r0,
 projectedPrimes:localRows.length,restrictedPrimes:thin.length,
 rowDensity:[String(numerator),String(denominator)],
 checked,closestK:firstK,realAnchor:String(A),stripBoundary:String(H),
 fixedY:String(bound),modulusY:String(M)
}));
