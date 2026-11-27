"use strict";
// Finite exact checks for totally-ramified local generator norms.
// This is toy arithmetic of canonical lattice coefficient classes.
const mod=(x,p)=>((x%p)+p)%p;
const sum=xs=>xs.reduce((a,b)=>a+b,0);
const energy=(v,p)=>p*sum(v.map(x=>x*x))-sum(v)**2;
function same(x,y,msg){checks++;if(x!==y)throw Error(msg+": "+x+" !== "+y);}
let checks=0;
function digitsW(r,p){let w=1;while(r){w*=1+r%p;r=Math.floor(r/p);}return w;}
function binoms(n,p) {
  const c=Array.from({length:n},()=>Array(n).fill(0));
  for(let i=0;i<n;i++) {
    c[i][0]=1;
    for(let j=1;j<=i;j++) c[i][j]=mod(c[i-1][j]+c[i-1][j-1],p);
  }
  return c;
}
function order(f,p,c){
  for(let j=0;j<f.length;j++) {
    let s=0;
    for(let i=j;i<f.length;i++)s+=c[i][j]*f[i];
    if(mod(s,p)!==0)return j;
  }
  return f.length;
}
function all(arrays,cb){
  const out=Array(arrays.length);
  function rec(i){if(i===arrays.length){cb(out);return;}
    for(const x of arrays[i]){out[i]=x;rec(i+1);}}
  rec(0);
}
function residues(p,n,cb){ const d=Array.from({length:p},(_,i)=>i);
  all(Array.from({length:n},()=>d),cb);
}
function canonicalEnergy(f,p,m){
  let result=0;
  for(let a=0;a<m;a++) result+=energy(Array.from({length:p-1},(_,b)=>f[a+b*m]||0),p);
  return m*result;
}
function fullFormula(p,m,k){return m*(p===2?1:2)*(p===2?1:3**Math.floor(k/m))*digitsW(k%m,p);}
function bruteBlock(res,p){
  let best=Infinity;
  const lifts=res.map(x=>[-p,0,p].map(z=>x+z));
  all(lifts,v=>{best=Math.min(best,energy(v,p));});
  return best;
}
// For each binary/ternary residue block, the theoretical lower bound
// really is attained on a small set of exact integer lifts.
for(const p of [2,3]) {
  const weight=new Map();
  residues(p,p-1,v=>{
    const predicted=(v.every(x=>x===0)?0:mod(sum(v),p)!==0?p-1:2*p);
    same(bruteBlock(v,p),predicted,"block lifts");
    weight.set(v.join(","),predicted);
  });
  for(const m of (p===2?[1,2,4,8,16]:[1,3])){
    const n=(p-1)*m,c=binoms(n,p);
    const min=Array(n+1).fill(Infinity);
    residues(p,n,f=>{
      const k=order(f,p,c);
      let e=0;
      for(let a=0;a<m;a++){
        let v=Array.from({length:p-1},(_,b)=>f[a+b*m]);
        e+=weight.get(v.join(","));
      }
      if(k<n) min[k]=Math.min(min[k],m*e);
    });
    min[n]=p*p*n;
    let max=1;
    for(let k=0;k<n;k++){
      const g=fullFormula(p,m,k), minL=Math.min(...min.slice(k));
      same(min[k],g,"full residue exact layer");
      const l=Math.min(p*p*n,...Array.from({length:n-k},(_,i)=>fullFormula(p,m,k+i)));
      same(minL,l,"lattice minimum");
      max=Math.max(max,g/minL);
    }
    same(max,Math.max(1,m/(p===2?4:3)),"largest gap");
  }
}
// Independent exact Hamming-order check.
for(const [p,m] of [[2,16],[3,9],[5,5],[7,7]]) {
  const min=Array(m).fill(Infinity),c=binoms(m,p);
  residues(p,m,f=>{
    const k=order(f,p,c);
    if(k<m)min[k]=Math.min(min[k],f.reduce((s,x)=>s+(x!==0),0));
  });
  for(let k=0;k<m;k++)same(min[k],digitsW(k,p),"Hamming at exact order");
}
// Explicit low-digit global-generator witness for binary/ternary depth.
function digitWitness(p,m,r) {
  let t=[1],place=1;
  while(r){
    const d=r%p;
    const factors=d===0?[[0,1]]:d===1?[[0,-1],[place,1]]:[[0,1],[place,1],[2*place,1]];
    const next=Array(t.length+factors.at(-1)[0]).fill(0);
    for(const [a,x] of factors)for(let i=0;i<t.length;i++)next[i+a]+=x*t[i];
    t=next;place*=p;r=Math.floor(r/p);
  }
  return t;
}
for(const p of [2,3])for(const m of p===2?[1,2,4,8,16,32,64]:[1,3,9,27,81]){
  const n=(p-1)*m,c=binoms(n,p);
  for(let k=0;k<n;k++) {
    const t=digitWitness(p,m,k%m),f=Array(n).fill(0);
    const j=Math.floor(k/m);
    for(let a=0;a<t.length;a++) {f[a]=(j?-1:1)*t[a];if(j)f[a+m]=t[a];}
    same(order(f,p,c),k,"digit witness exact order");
    same(canonicalEnergy(f,p,m),fullFormula(p,m,k),"digit witness canonical norm");
  }
}
// The all-prime top-block constant and witnessed upper bound.
for(const p of [2,3,5,7,11]) {
  const basis=binoms(p-1,p)[p-2].map((x,b)=>mod((-1)**(p-2-b)*x,p));
  const C=p*p*(p*p-1)/12;
  for(let c=1;c<p;c++){
    const v=basis.map(x=>mod(c*x,p));
    same(new Set([...v,0]).size,p,"all residue classes occur");
    same(sum(Array.from(new Set([...v,0]))),
      p*(p-1)/2,"permutes all residues");
    same(bruteBlock(v,p),C,"consecutive lifts are minimal");
  }
  for(const m of [1,p,p*p]){
    const n=(p-1)*m,c=binoms(n,p);
    const d=binoms(m,p);
    const g=Array.from({length:n},(_,i)=>i<m?1:0);
    same(order(g,p,c),m-1,"geometric-sum exact order");
    same(canonicalEnergy(g,p,m),(p-1)*m*m,"geometric-sum exact norm");
    const b=Array(n).fill(0);
    b[0]=p===2?-2:-1;if(p!==2)b[m]=1;
    same(order(b,p,c),m,"next layer witness order");
    same(canonicalEnergy(b,p,m),2*p*m,"next layer witness norm");
    for(let r=0;r<m;r++){
      if(m>20 && r!==0 && r!==1 && r!==m-2 && r!==m-1)continue;
      const f=Array(n).fill(0);
      for(let a=0;a<=r;a++){
        const lab=mod((-1)**(r-a)*d[r][a],p);
        for(let b=0;b<p-1;b++)f[a+b*m]=mod(lab*basis[b],p);
      }
      same(order(f,p,c),(p-2)*m+r,"top layer exact order");
      same(canonicalEnergy(f,p,m),m*C*digitsW(r,p),"top layer exact norm");
    }
  }
}
console.log("OK: "+checks+" exact checked identities and finite minima.");
