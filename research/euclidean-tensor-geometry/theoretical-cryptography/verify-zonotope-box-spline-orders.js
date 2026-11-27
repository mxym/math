'use strict';
/* Exact integer/rational replay of the covariance and signed-part identities.
 * The proof covers arbitrary real generators. No packages or input data. */
const assert = require('node:assert/strict');
const abs = x => x < 0n ? -x : x;
const sign = x => x < 0n ? -1n : x > 0n ? 1n : 0n;
const sum = xs => xs.reduce((a,b) => a+b, 0n);
const product = xs => xs.reduce((a,b) => a*b, 1n);
function gcd(a,b) { a=abs(a); b=abs(b); while(b) [a,b]=[b,a%b]; return a; }
function q(n,d=1n) {
  assert.notEqual(d,0n); if(d<0n){n=-n;d=-d;} const g=gcd(n,d);return [n/g,d/g];
}
const plus=(a,b)=>q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const minus=(a,b)=>q(a[0]*b[1]-b[0]*a[1],a[1]*b[1]);
const times=(a,b)=>q(a[0]*b[0],a[1]*b[1]);
const dot=(a,b)=>sum(a.map((x,j)=>x*b[j]));
const colset=(a,j,y)=>a.map((x,i)=>i===j ? y:x);
const all=(n)=>Array.from({length:n},(_,j)=>j);
function choices(a,k) {
  const out=[]; function rec(i,b){if(b.length===k){out.push(b);return;}
    for(let j=i;j<=a.length-k+b.length;j++) rec(j+1,[...b,a[j]]);}
  rec(0,[]); return out;
}
// The vectors are stored as rows, so replacing a basis vector is a row replacement.
// Bareiss invariant gives exact determinant, including signed pivot exchanges.
function det(rows) {
  const A=rows.map(v=>v.slice()),n=A.length;
  if(!n)return 1n; let prev=1n,parity=1n;
  for(let k=0;k<n-1;k++){
    let p=k;while(p<n&&!A[p][k])p++;if(p===n)return 0n;
    if(p!==k){[A[p],A[k]]=[A[k],A[p]];parity=-parity;}
    const v=A[k][k];
    for(let i=k+1;i<n;i++){for(let j=k+1;j<n;j++){
      const x=A[i][j]*v-A[i][k]*A[k][j];
      assert.equal(x%prev,0n); A[i][j]=x/prev;
    } A[i][k]=0n;} prev=v;
  }
  return parity*A[n-1][n-1];
}
function dualModel(M) {
  const d=M.length,r=M[0].length,n=d+r;
  const G=all(n).map(j=>all(d).map(i=>j<d ? BigInt(j===i):M[i][j-d]));
  const B=all(n).map(j=>all(r).map(i=>j<d ? -M[j][i]:BigInt(j===d+i)));
  return {d,r,n,G,B};
}
let checks=0; function ck(x,y){assert.deepEqual(x,y);checks++;}
function makeTiling(model,rev=false) {
  const {d,r,n,G,B}=model, ix=all(n),J0=choices(ix,r);
  let dir,tiles;
  for(let t=2n;t<=10000n;t++){
    dir=all(r).map(k=>(rev?-1n:1n)*t**BigInt(k));
    tiles=[];let ok=true;
    for(const J of J0){
      const A=J.map(j=>B[j]),D=det(A);
      const I=ix.filter(i=>!J.includes(i)); ck(abs(D),abs(det(I.map(i=>G[i]))));
      if(!D)continue;
      const ss=J.map((j,k)=>sign(det(colset(A,k,dir))*D));
      if(ss.includes(0n)){ok=false;break;}
      tiles.push({J,I,v:abs(D),ss});
    }
    if(ok)return {dir,tiles,V:sum(tiles.map(x=>x.v))};
  }
  throw Error('no generic direction in checked range');
}
function quotientData(model,dir){
  const {r,n,B}=model,ix=all(n);
  if(r<2)return [];
  return choices(ix,r-2).flatMap(S=>{
    const BS=S.map(j=>B[j]);
    const perp=all(r).map(i=>all(r).map(j=>BigInt(i===j)));
    for(const e of perp){
      const D=det([...BS,dir,e]); if(!D)continue;
      const J=ix.filter(j=>!S.includes(j)), entries=J.flatMap(j=>{
        const x=det([...BS,B[j],e]), y=det([...BS,dir,B[j]]);
        if(!y){ck(x,0n);return [];}
        return [{j,x,y,t:q(x,y)}];
      }).sort((a,b)=>Number(sign(a.t[0]*b.t[1]-b.t[0]*a.t[1])));
      return [{S,D,entries}];
    }
    return [];
  });
}
function checkVar(model,tiling,dual,u){
  const a=model.G.map(g=>dot(g,u));
  const T=tiling.tiles, V=tiling.V;
  const total=V*sum(a.map(x=>x*x));
  const v12=sum(T.map(t=>t.v*(sum(t.I.map(j=>a[j]**2n))+3n*sum(t.J.map((j,k)=>a[j]*t.ss[k]))**2n)));
  const endpoint=sum(T.map(t=>t.v*sum(t.J.map(j=>a[j]**2n))));
  const groups=new Map();
  for(const t of T)for(const [i,j] of choices(all(t.J.length),2)){
    const S=t.J.filter((_,k)=>k!==i&&k!==j).join(',');
    groups.set(S,(groups.get(S)||0n)+t.v*t.ss[i]*t.ss[j]*a[t.J[i]]*a[t.J[j]]);
  }
  for(const {S,D,entries} of dual){
    let pref=0n,E=q(0n);
    for(let l=0;l<entries.length;l++){
      const x=entries[l]; pref+=x.y*a[x.j];
      if(l+1<entries.length)E=plus(E,times(q(pref*pref),minus(entries[l+1].t,x.t)));
    }
    ck(pref,0n);E=times(E,q(1n,abs(D)));
    ck(E,q(groups.get(S.join(','))||0n)); assert(E[0]>=0n);
  }
  for(const [k,v] of groups){if(v)assert(dual.some(x=>x.S.join(',')===k));}
  ck(v12-total,2n*endpoint+6n*sum([...groups.values()]));
  ck(v12===total,model.B.every((b,j)=>b.every(x=>x===0n)||a[j]===0n));
  assert(v12>=total);
  return v12;
}
function nextGen(seed){return ()=>{seed=(1664525*seed+1013904223)>>>0;return seed;};}
const rng=nextGen(1337);
for(let trial=0;trial<120;trial++){
  const d=1+trial%4,r=1+Math.floor(trial/4)%5;
  const model=dualModel(all(d).map(()=>all(r).map(()=>BigInt(rng()%11-5))));
  const A=makeTiling(model), Z=makeTiling(model,true), Q=quotientData(model,A.dir);
  ck(A.V,Z.V);ck(A.tiles.length,Z.tiles.length);
  for(let j=0;j<A.tiles.length;j++)ck(A.tiles[j].ss,Z.tiles[j].ss.map(s=>-s));
  for(let j=0;j<7;j++){
    const u=all(d).map((i)=>j<d?BigInt(i===j):BigInt(rng()%15-7));
    ck(checkVar(model,A,Q,u),checkVar(model,Z,Q,u));
  }
}
// Full convex-order expansion can be tested on random ridge polynomials because
// powers of linear forms span each homogeneous polynomial space.
function fact(n){let p=1n;for(let j=2;j<=n;j++)p*=BigInt(j);return p;}
function conv(a,b){return a.map((_,k)=>a.slice(0,k+1).reduce((p,v,j)=>plus(p,times(v,b[k-j])),q(0n)));}
function mgfCoeff(a,L,kind){
  return all(L+1).map(k=>kind==='sign' ? q(a**BigInt(k),2n**BigInt(k)*fact(k)):
    k%2 ? q(0n):q(a**BigInt(k),2n**BigInt(k)*(kind==='box'?fact(k+1):fact(k))));
}
for(let r=1;r<=3;r++)for(let d=1;d<=3;d++)for(let trial=0;trial<4;trial++){
  const m=dualModel(all(d).map(()=>all(r).map(()=>BigInt(rng()%7-3))));
  const T=makeTiling(m), a=m.G.map(g=>dot(g,all(d).map(j=>BigInt(j+1))));
  // A common u must be used for all generators; the choice above is deterministic.
  const L=6, zero=()=>all(L+1).map(()=>q(0n)), add=(a,b)=>a.map((x,k)=>plus(x,b[k]));
  const mul=(a,s)=>a.map(x=>times(x,q(s))), one=zero();one[0]=q(1n);
  const law=(keys,kind)=>keys.reduce((curr,[j,v])=>conv(curr,mgfCoeff(a[j]*v,L,kind)),one);
  const box=(keys)=>law(keys.map(j=>[j,1n]),'box');
  const endpoints=(keys)=>law(keys.map(j=>[j,1n]),'endpoint');
  let th=zero(), ep=zero(), cor=zero();
  for(const t of T.tiles){
    const boxI=box(t.I),key=t.J.map((j,k)=>[j,t.ss[k]]);
    const f=law(key,'sign'),fr=law(key.map(([j,s])=>[j,-s]),'sign');
    const mix=add(f,fr).map(v=>times(v,q(1n,2n)));
    th=add(th,mul(conv(boxI,mix),t.v));
    ep=add(ep,mul(conv(boxI,endpoints(t.J)),t.v));
    for(const [i,j] of choices(all(t.J.length),2)){
      const S=t.J.filter((_,k)=>k!==i&&k!==j),keys=all(m.n).filter(k=>!S.includes(k));
      const h=conv(box(keys),endpoints(S));
      const coef=q(t.v*t.ss[i]*t.ss[j]*a[t.J[i]]*a[t.J[j]],4n);
      cor=add(cor,[q(0n),q(0n),...h.slice(0,L-1).map(v=>times(v,coef))]);
    }
  }
  ck(th,add(ep,cor));
  for(let k=0;k<=L;k+=2){assert(minus(th[k],ep[k])[0]>=0n);}
}

for(let trial=0;trial<36;trial++){
  const r=1+trial%5,m=dualModel(all(2).map(()=>all(r).map(()=>BigInt(rng()%9-4))));
  const T=makeTiling(m),L=8,zero=()=>all(L+1).map(()=>q(0n));
  const add=(a,b)=>a.map((v,k)=>plus(v,b[k]));
  const mul=(a,s)=>a.map(v=>times(v,s));
  const a=m.G.map(g=>g[0]),W=l=>mgfCoeff(l,L,'box');
  let y=zero();
  for(const t of T.tiles){
    const ctr=sum(t.J.map((j,k)=>a[j]*t.ss[k]));
    const row=t.I.reduce((p,j)=>conv(p,W(a[j])),mgfCoeff(ctr,L,'sign'));
    y=add(y,mul(row,q(t.v)));
  }
  const active=m.G.filter(g=>g[0]!==0n).map(g=>[abs(g[0]),q(g[1],g[0])]);
  active.sort((a,b)=>Number(sign(minus(a[1],b[1])[0])));
  const total=sum(active.map(g=>g[0]));
  const w0=sum(m.G.filter(g=>!g[0]).map(g=>abs(g[1])));
  let area=q(w0*total),mix=mul(W(total),area),p=0n;
  for(let j=0;j+1<active.length;j++){
    p+=active[j][0];
    const mass=times(minus(active[j+1][1],active[j][1]),q(p*(total-p)));
    area=plus(area,mass);
    mix=add(mix,mul(conv(W(p),W(total-p)),mass));
  }
  ck(area,q(T.V));ck(y,mix);
}

const rows=[
 [6,-3,-1,-6],[-4,1,1,-3],[0,-2,-4,6],[-3,6,5,5],
 [-4,5,-1,4],[4,7,-2,-7],[2,-5,1,4],[-1,-9,1,-3]
].map(row=>row.map(BigInt));
ck(all(4).map(j=>sum(rows.map(r=>r[j]))),[0n,0n,0n,0n]);
const d0=[1n,0n,0n,0n], counts=all(5).map(()=>0n), masses=counts.slice();
for(const J of choices(all(8),4)){
  const A=J.map(j=>rows[j]),D=det(A);assert(D);
  const sg=all(4).map(j=>sign(det(colset(A,j,d0))*D));assert(!sg.includes(0n));
  const k=sg.filter(s=>s<0n).length; counts[k]++; masses[k]+=abs(D);
}
ck(counts,[7n,17n,20n,16n,10n]);
ck(masses,[8344n,20155n,23033n,20155n,8344n]);
ck(sum(masses.map((x,j)=>j%2?-x:x)),-589n);
console.log('PASS: '+checks+' exact checks; rank-4 signed coefficient = -589');
