"use strict";
// Fixed finite identities, not estimates for L-functions or class-group computations.
const assert=(ok,text)=>{if(!ok)throw Error(text);};
const mod=(a,p)=>(a%p+p)%p;
const eq=(x,y)=>x===y;
const conjugate=([a,b])=>[a,-b];
const mul=(f,[a,b],[c,d])=>[a*c+f*b*d,a*d+b*c];
const neg=([a,b])=>[-a,-b];
const powmod=(a,n,p)=>{
  let b=mod(a,p), z=1;
  while(n){if(n%2===1)z=z*b%p;b=b*b%p;n=Math.floor(n/2);}
  return z;
};
const leg=(a,p)=>{
  const v=powmod(a,(p-1)/2,p);
  return v===p-1?-1:v;
};
const fixed=[17,41,73,89,97,113,137,193,233,241,257,281,
 313,337,353,401,409,433,449,457,521,569,577,593,601,617,
 641,673,761,769,809,857,881,929,937,953,977];
const sqrtInt=n=>Math.floor(Math.sqrt(n));
const fixtureMap=(f,p)=>{
  const d=-f;
  for(let b=2;b*b*d<p;b+=2) {
    const a=sqrtInt(p-d*b*b);
    if(a*a+d*b*b!==p || a%2===0) continue;
    let g=[a,b];
    const wanted=f===-1||b%4===0?1:3;
    if(a%4!==wanted) g=neg(g);
    return g;
  }
  throw Error("missing fixed representation");
};
const isPrimeSmall=n=>{
  for(let d=2;d*d<=n;d++)if(n%d===0)return false;
  return n>=2;
};
const emb=(p,[a,b])=>mod(-a*powmod(b,p-2,p),p);
let counts={fixtures:0,conjugateSigns:0,spinSigns:0,dyadicLocalSquares:0,
            rowPrefixes:0,rowWeights:0};
for(const f of [-1,-2]){
  const theta=f===-1?[1,1]:[0,1];
  const reps=new Map(fixed.map(p=>[p,fixtureMap(f,p)]));
  for(const p of fixed) {
    assert(isPrimeSmall(p)&&p%8===1,"fixed prime norm");
    const w=reps.get(p), [a,b]=w;
    const n=mul(f,w,conjugate(w));
    assert(n[0]===p&&n[1]===0,"norm");
    const wanted=f===-1||b%4===0?[1,0]:mul(f,[1,1],[1,1]);
    assert(mod(a-wanted[0],4)===0&&mod(b-wanted[1],4)===0,"square modulo 4");
    const R=emb(p,w);
    assert(mod(R*R-f,p)===0&&mod(a+b*R,p)===0,"residue field");
    counts.fixtures+=4;
    const G=([a,b])=>leg(a+b*R,p);
    const H=([a,b])=>leg(a-b*R,p);
    assert(G(theta)===H(theta),"sigma independent of the chosen ideal");
    assert(G(theta)*G(conjugate(theta))===leg(2,p),"norm identity at 2");
    counts.conjugateSigns+=2;
    for(const q of fixed)if(q!==p) {
      const z=reps.get(q), A=leg(q,p), m=G(conjugate(w)), B=m*G(z);
      assert(A===leg(p,q),"rational reciprocity");
      assert(m*m===1&&B*B===1,"no degenerate spin");
      assert(B===G(mul(f,conjugate(w),z)),"row multiplier");
      assert(A*B===m*G(conjugate(z)),"mixed sign is conjugated spin");
      for(const s of [-1,1])for(const t of [-1,1]){
        assert((1+s*A)*(1+t*B)===4*Number(A===s&&B===t),"joint sign extraction");
        counts.spinSigns++;
      }
      counts.spinSigns+=4;
    }
  }
}
// Check products of congruent local units modulo t^5 for finite quotients.
// Since (t)^8=(16) in these three rings, this tests squarehood mod t^8.
for(const f of [-1,-2,2]){
  const T=f===-1?[1,1]:[0,1];
  let tk=[1,0];
  for(let i=0;i<5;i++)tk=mul(f,tk,T);
  const isDivisible=([a,b],d)=>{
    const [c,e]=mul(f,[a,b],conjugate(d));
    const N=mul(f,d,conjugate(d))[0];
    return c%N===0&&e%N===0;
  };
  const all=[];
  for(let a=0;a<16;a++)for(let b=0;b<16;b++)all.push([a,b]);
  const units=all.filter(g=>!isDivisible(g,T));
  const key=([a,b])=>mod(a,16)*16+mod(b,16);
  const squares=new Set(units.map(g=>key(mul(f,g,g))));
  for(const g of units) for(const h of units) {
    if(!isDivisible([g[0]-h[0],g[1]-h[1]],tk)) continue;
    assert(squares.has(key(mul(f,g,h))),"equal dyadic unit class gives a square product");
    counts.dyadicLocalSquares++;
  }
}

function dyadicPrefix(hi,n) {
  const blocks=[];
  let a=0;
  for(let length=n;length>=1;length/=2)if(a+length<=hi) {
    blocks.push([a,a+length,length]);a+=length;
  }
  return blocks;
}
for(let columns=1;columns<=11;columns++){
  const N=2**Math.ceil(Math.log2(columns));
  for(let p=0;p<=columns;p++)for(let q=0;q<=columns;q++)for(let r=0;r<=columns;r++){
    const cut=[p,q,r], levels=new Map(), mat=cut.map(()=>Array(columns).fill(0));
    for(const [i,bound] of cut.entries())for(const [a,b,d] of dyadicPrefix(bound,N)) {
      if(!levels.has(d))levels.set(d,new Map());
      const blocks=levels.get(d);
      if(!blocks.has(a))blocks.set(a,[]);
      blocks.get(a).push(i);
      for(let c=a;c<b;c++)mat[i][c]++;
    }
    for(let i=0;i<cut.length;i++)for(let j=0;j<columns;j++)
      assert(eq(mat[i][j],Number(j<cut[i])),"prefix matrix identity");
    for(const [d,m] of levels){
      const rows=new Set(), cols=new Set();
      let l1=0,l2=0;
      for(const [a,rr] of m){
        for(const i of rr){assert(!rows.has(i),"rows disjoint on a layer");rows.add(i);}
        for(let j=a;j<a+d;j++){assert(!cols.has(j),"cols disjoint on a layer");cols.add(j);}
        l1+=rr.length;l2+=d;
        counts.rowWeights++;
      }
      assert(l1<=cut.length&&l2<=columns,"level Cauchy budgets");
    }
    counts.rowPrefixes++;
  }
}
console.log({...counts,total:Object.values(counts).reduce((a,b)=>a+b,0)});
