// Run with Node.js: node verify.js
"use strict";
const assert=require("node:assert/strict");
const mod=(x,p)=>(x%p+p)%p;
function inv(x,p){let a=1,e=p-2;while(e){if(e&1)a=a*x%p;e>>=1;x=x*x%p;}return a;}
function rank(M,p){
  let r=0,n=M.length;
  for(let j=0;j<n;j++){
    let i=r;while(i<n&&!M[i][j])i++;
    if(i===n)continue;
    [M[i],M[r]]=[M[r],M[i]];
    const a=inv(M[r][j],p);
    assert.equal(a*M[r][j]%p,1);
    for(let k=r+1;k<n;k++){
      const b=M[k][j]*a%p;if(!b)continue;
      for(let w=j;w<n;w++)M[k][w]=mod(M[k][w]-b*M[r][w],p);
    }
    r++;
  }
  return r;
}
function orbits(s,mu){
  const R=[];
  for(let z=0;z<3**s;z++){
    let a=z,w=[],sum=0;
    for(let i=0;i<s;i++){const v=a%3-1;w.push(v);sum+=v;a=Math.floor(a/3);}
    if(sum)continue;
    let reps=[w],ok=true;
    for(let k=1;k<s;k++){
      const j=w.slice(k).concat(w.slice(0,k));
      const v=j.reduceRight((a,b)=>3*a+b+1,0);
      if(v===z)break;
      if(v<z){ok=false;break;}
      reps.push(j);
    }
    if(ok&&(mu===1||reps.length%2===0))R.push(reps);
  }
  return R;
}
function transfer(v,w,u,p){
  let R=0;
  for(const b of [0,1]){
    let t=b,c=1;
    for(let k=0;k<w.length;k++){
      const e=v[k]-w[k];
      if(e===0)c*=u+(1-2*t)*w[k];
      else if(t+e===0||t+e===1){c*=w[k]===0?2:1;t+=e;}
      else{c=0;break;}
      if(!c)break;
    }
    if(t===b)R+=c;
  }
  return mod(R,p);
}
function rawTrace(v,w,p){
  let R=0;
  for(const b of [0,1]){
    let t=b,c=1;
    for(let k=0;k<w.length;k++){
      for(const a of [w[k],-v[k]]){
        if(a===0){if(t)c=c*7%p;}
        else if(t+a===0||t+a===1)t+=a;
        else c=0;
      }
    }
    if(t===b)R+=c;
  }
  return mod(R,p);
}
const gcd=(a,b)=>b?gcd(b,a%b):a;
function neutral(s){
  let row=[1n];
  for(let j=0;j<s;j++){
    const next=Array(row.length+2).fill(0n);
    for(let i=0;i<row.length;i++)for(let a=0;a<3;a++)next[i+a]+=row[i];
    row=next;
  }
  return row[s];
}
function dim(s){
  let a=0n;
  for(let j=0;j<s;j++)a+=BigInt((-1)**((s+1)*j))*neutral(gcd(s,j));
  assert.equal(a%BigInt(s),0n);
  return a/BigInt(s);
}
let defect=0n;
for(let s=1;s<=10;s++){
  const mu=(-1)**(s+1),o=orbits(s,mu);
  const matrix=(g,p)=>o.map(v=>o.map(w=>mod(w.reduce((a,z,j)=>a+mu**j*g(v[0],z),0),p)));
  const p=2521,a=rank(matrix((v,w)=>transfer(v,w,0,p),p),p),b=rank(matrix((v,w)=>transfer(v,w,1,p),p),p);
  assert.equal(BigInt(o.length),dim(s));
  assert.equal(BigInt(a),defect);
  assert.equal(a+b,o.length);
  const raw=s%2?rank(matrix((v,w)=>rawTrace(v,w,251),251),251):null;
  if(raw!==null)assert.equal(raw,b);
  process.stdout.write(JSON.stringify({s,dim:o.length,T0:a,T1:b,raw,maxrank:3**s-a})+"\n");
  defect=dim(s)-defect;
}

const eps=(i,j,k)=>i===j||j===k||i===k?0:(j-i+3)%3===1?1:-1;
const inds=[0,1,2], P=i=>[0,...inds.map(j=>+(i===j))];
const add=(a,b)=>a.map((x,i)=>x+b[i]), scale=(a,c)=>a.map(v=>v*c);
const mul=(a,b)=>[
  a[0]*b[0]-inds.reduce((t,i)=>t+a[i+1]*b[i+1],0),
  ...inds.map(k=>a[0]*b[k+1]+b[0]*a[k+1]
    -inds.reduce((s,i)=>s+inds.reduce((t,j)=>t+eps(i,j,k)*a[i+1]*b[j+1],0),0))
];
const L=(u,i,j)=>[u*(i===j),...inds.map(k=>eps(i,j,k))];
for(const u of [-1,0,1,2])for(const i of inds)for(const j of inds)for(const k of inds){
  let lhs=[0,0,0,0];
  for(const a of inds){
    lhs=add(lhs,scale(L(u,a,k),-(u*u-1)*eps(i,j,a)));
    for(const b of inds)lhs=add(lhs,scale(mul(L(u,i,a),L(u,j,b)),u*eps(a,b,k)));
  }
  const rhs=scale(add(mul(L(u,i,k),P(j)),mul(P(i),L(u,j,k))),-1);
  assert.deepEqual(lhs.map(x=>x||0),rhs.map(x=>x||0));
}
process.stdout.write("Checked the local quaternion identity at four interpolation points for all 27 index triples.\n");
