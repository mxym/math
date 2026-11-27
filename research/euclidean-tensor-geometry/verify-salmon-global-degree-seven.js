#!/usr/bin/env node
'use strict';
const p=257,mod=x=>(x%p+p)%p,inv=Array(p).fill(0);
for(let i=1;i<p;i++)for(let j=1;j<p;j++)if(i*j%p===1)inv[i]=j;
const assert=(b,m)=>{if(!b)throw Error(m)};
function part(d,max=d,L=Infinity){if(!d)return [[]];if(!L)return [];return Array.from({length:Math.min(d,max)},(_,i)=>i+1).reverse().flatMap(a=>part(d-a,a,L-1).map(b=>[a,...b]));}
const fact=n=>Array.from({length:n},(_,i)=>i+1).reduce((a,b)=>a*b,1);
const key=a=>a.join("");
const tabCache=new Map(),charCache=new Map();
function tabs(a){
 const K=key(a);
 if(tabCache.has(K))return tabCache.get(K);
 const d=a.reduce((x,y)=>x+y,0),c=a.map(()=>0),rows=[];
 function gen(t){
  if(t.length===d){rows.push(t);return;}
  for(let r=0;r<a.length;r++) if(c[r]<a[r]&&(!r||c[r]<c[r-1])){
    c[r]++;gen(t.concat(r));c[r]--;
  }
 }
 gen([]);
 const ind=new Map(rows.map((t,i)=>[key(t),i]));
 const ops=Array.from({length:d-1},(_,i)=>rows.map((t,k)=>{
    const con=t.map((r,j)=>t.slice(0,j).filter(s=>s===r).length-r);
    const dd=con[i+1]-con[i],q=t.slice();
    [q[i],q[i+1]]=[q[i+1],q[i]];
    const r=t[i]===t[i+1]?undefined:ind.get(key(q)), x=inv[mod(dd)];
    assert(x!==0,"zero content gap");
    return r===undefined?[[k,x]]:[[k,x],[r,mod(1+x)]];
 }));
 const R={a,d,rows,ind,ops,N:rows.length};
 tabCache.set(K,R);return R;
}
function words(c){
 let pos=0;const ans=[];
 for(const n of c){for(let j=0;j<n-1;j++)ans.push(pos+j);pos+=n;}
 return ans;
}
function scalarAct(v,op){
 let w=new Int32Array(v.length);
 for(let i=0;i<v.length;i++)if(v[i])for(const [j,c]of op[i])w[j]=(w[j]+v[i]*c)%p;
 return w;
}
function character(A,c){
 const K=key(A.a)+":"+key(c);if(charCache.has(K))return charCache.get(K);
 let tr=0;const w=words(c);
 for(let k=0;k<A.N;k++){let v=new Int32Array(A.N);v[k]=1;for(const i of w)v=scalarAct(v,A.ops[i]);tr+=v[k];}
 tr=mod(tr);if(tr>p/2)tr-=p;
 assert(Math.abs(tr)<=A.N,"bad character");
 charCache.set(K,tr);return tr;
}
function kronecker(A){
 const d=A[0].d;let sum=0;
 for(const c of part(d)){let z=1;for(let j=1;j<=d;j++){const n=c.filter(x=>x===j).length;z*=j**n*fact(n);}
 sum+=fact(d)/z*A.reduce((s,a)=>s*character(a,c),1);}
 assert(sum%fact(d)===0&&sum>=0,"nonintegral Kronecker multiplicity");
 return sum/fact(d);
}
function action(v,A,i,mode) {
 const tail=A.slice(mode+1).reduce((x,t)=>x*t.N,1),t=A[mode],n=t.N,size=v.length;
 const w=new Int32Array(size);
 for(let k=0;k<size;k++)if(v[k]){
  const z=Math.floor(k/tail)%n;
  for(const [j,c] of t.ops[i][z]){const q=k+(j-z)*tail;w[q]=(w[q]+v[k]*c)%p;}
 }return w;
}
function average(v,A,start,k,modes){
 for(let m=2;m<=k;m++){
  let s=v.slice(),w=v;
  for(let i=start+m-2;i>=start;i--){for(const axis of modes)w=action(w,A,i,axis);for(let j=0;j<s.length;j++)s[j]=(s[j]+w[j])%p;}
  v=s.map(x=>x*inv[m]%p);
 }return v;
}
function basisReduce(v,base,w=null){
 for(const b of base){const f=v[b.j];if(f){for(let i=b.j;i<v.length;i++)v[i]=mod(v[i]-f*b.v[i]);if(w)for(let i=0;i<w.length;i++)w[i]=mod(w[i]-f*b.w[i]);}}
 const j=v.findIndex(x=>x);
 if(j<0)return false;
 const invx=inv[v[j]];
 v=v.map(x=>x*invx%p);
 if(w)w=w.map(x=>x*invx%p);
 base.push({j,v,w});
 return true;
}
const axes=[0,1,2];
function ambient(A){
 const d=A[0].d,g=kronecker(A),N=A.reduce((x,a)=>x*a.N,1),base=[];
 let seed=123456789; for(let k=0;k<g+4&&base.length<g;k++){let v=new Int32Array(N);for(let j=0;j<N;j++){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;v[j]=(seed>>>0)%p;}basisReduce(average(v,A,0,d,axes),base);}
 for(let k=0;k<N&&base.length<g;k++){
   let v=new Int32Array(N);v[k]=1;
   basisReduce(average(v,A,0,d,axes),base);
 }
 assert(base.length===g,"invariant basis count");
 return base.map(x=>x.v);
}
function image(v,A,sizes){
 let x=v,st=0;
 for(const n of sizes){if(n>1)for(const ax of axes)x=average(x,A,st,n,[ax]);st+=n;}
 return x;
}
function ideal(A,ambientBasis,sizes){
 const im=[],kernel=[],N=ambientBasis[0]?.length;
 for(const v of ambientBasis){
  const g=new Int32Array(N*sizes.length);
  for(let j=0;j<sizes.length;j++)g.set(image(v,A,sizes[j]),j*N);
  const w=v.slice();
  if(!basisReduce(g,im,w))kernel.push(w);
 }return kernel;
}
function embed(A,B,rows,v){
 const ids=B.map((x,i)=>x.rows.map(T=>A[i].ind.get(key(T.concat(rows[i])))));
 assert(ids.every(x=>x.every(i=>i!==undefined)),"bad embedding");
 const X=new Int32Array(A.reduce((x,a)=>x*a.N,1));
 for(let k=0;k<v.length;k++)if(v[k]){
  const a=Math.floor(k/(B[1].N*B[2].N)),b=Math.floor(k/B[2].N)%B[1].N,c=k%B[2].N;
  X[(ids[0][a]*A[1].N+ids[1][b])*A[2].N+ids[2][c]]=v[k];
 }return X;
}

const strassen=a=>a.map(x=>key(x)).sort().join(",")==="2111,2111,311";
const sixType=a=>a.map(x=>key(x)).sort().join(",")==="222,222,3111";
const smaller=A=>A.a.flatMap((n,i)=>n>(A.a[i+1]||0)?[{row:i,a:A.a.map((x,t)=>t===i?x-1:x).filter(Boolean)}]:[]);
const by4=d=>part(d,d,4).filter(x=>x.length===4);
const cacheU=new Map(),knownCache=new Map();
function uSpace(A){
 const K=A.map(x=>key(x.a)).join("/");
 if(!cacheU.has(K))cacheU.set(K,ambient(A));
 return cacheU.get(K);
}
function known(A){
 const K=A.map(x=>key(x.a)).join("/");
 if(knownCache.has(K))return knownCache.get(K);
 const d=A[0].d,S=A.map(x=>x.a),R=[];
 if(d===5&&strassen(S)||d===6&&sixType(S)){
  const s=ideal(A,uSpace(A),by4(d));
  assert(s.length===1,"seed line not detected");
  for(const v of s)basisReduce(v.slice(),R);
 }
 if(d>5){
  const opts=A.map(smaller);
  for(const x of opts[0])for(const y of opts[1])for(const z of opts[2]){
   const B=[x.a,y.a,z.a].map(tabs);
   for(const v of known(B))basisReduce(average(embed(A,B,[x.row,y.row,z.row],v),A,0,d,axes),R);
  }
 }
 const b=R.map(x=>x.v);knownCache.set(K,b);return b;
}
function check(d){
 let total=0,nonzero=0,missing=[];const P=part(d,d,4);
 for(let i=0;i<P.length;i++)for(let j=i;j<P.length;j++)for(let k=j;k<P.length;k++){
  const S=[P[i],P[j],P[k]];
  if(S.filter(x=>x.length===4).length<2)continue;
  const A=S.map(tabs),base=uSpace(A);
  const upper=ideal(A,base,by4(d)).length, lower=known(A).length;
  if(upper!==lower){
   missing.push({S,g:base.length,upper,lower});
   console.log({S,g:base.length,upper,lower});
  }
  total++;nonzero+=upper;
 }
 const expected={5:[6,1],6:[25,9],7:[58,48]}[d];
 assert(expected&&total===expected[0]&&nonzero===expected[1]&&missing.length===0,JSON.stringify({d,total,nonzero,missing}));
 console.log({d,total,nonzero,missing:missing.length});
}
for(let d=5;d<=7;d++)check(d);
