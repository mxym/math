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
const expected=[[3,0,3],[5,3,2],[11,2,9],[23,9,14],[57,14,43],[141,43,98],[351,98,253]];
for(let s=3;s<=9;s++){
  const mu=(-1)**(s+1),o=orbits(s,mu);
  const matrix=(g,p)=>o.map(v=>o.map(w=>mod(w.reduce((a,z,j)=>a+mu**j*g(v[0],z),0),p)));
  const p=2521,a=rank(matrix((v,w)=>transfer(v,w,0,p),p),p),b=rank(matrix((v,w)=>transfer(v,w,1,p),p),p);
  assert.deepEqual([o.length,a,b], expected[s-3]);
  assert.equal(a+b,o.length);
  const raw=s%2?rank(matrix((v,w)=>rawTrace(v,w,251),251),251):null;
  if(raw!==null)assert.equal(raw,b);
  process.stdout.write(JSON.stringify({s,dim:o.length,T0:a,T1:b,raw,rank:3**s-a})+"\n");
}
