'use strict';
// Fixed small quantization identities and finite rational examples only.
let exact=0,numeric=0;
function check(ok,label){if(!ok)throw Error(label);exact++;}
function near(x,y,tol,label){if(!Number.isFinite(x)||!Number.isFinite(y)||Math.abs(x-y)>tol)throw Error(label+': '+x+' vs '+y);numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const sum=a=>a.reduce((x,y)=>x+y,0);
const key=v=>v.join(',');
const mod=(x,d)=>((x%d)+d)%d;
let seed=0x48162a4b;
function gen(n){seed=(Math.imul(1664525,seed)+1013904223)>>>0;return (seed>>>8)%n;}
function visit(values,n,f,p=[]){
 if(!n){f(p);return;}
 for(const v of values){p.push(v);visit(values,n-1,f,p);p.pop();}
}
function pairs(n){const p=[];for(let j=1;j<n;j++)for(let i=0;i<j;i++)p.push([i,j]);return p;}
function norm(v){const m=Math.min(...v);return v.map(x=>x-m);}
function threshold(f,d,u){return norm(f.map(a=>(a+u>=d)?1:0));}
function phaseChain(f){
 const order=seq(f.length).sort((a,b)=>f[b]-f[a]), a=Array(f.length).fill(0), C=[a.slice()];
 for(let j=0;j<f.length-1;j++){a[order[j]]=1;C.push(a.slice());}
 return {order,C};
}
function allowed(w,f,i,j){
 const d=w[i]-w[j];return d===0||(f[i]>f[j]?d===1:d===-1);
}
// A complete set of edges or one missing edge: exhaustive support patterns.
for(let N=3;N<=7;N++){
 const ps=pairs(N),states=[];
 visit([0,1,2],N,w=>{if(Math.min(...w)===0)states.push(w.slice());});
 for(let run=0;run<9;run++){
   const order=seq(N);
   for(let j=N-1;j>0;j--){const k=gen(j+1);[order[j],order[k]]=[order[k],order[j]];}
   const f=Array(N);for(let j=0;j<N;j++)f[order[j]]=1+3*j;
   const data=phaseChain(f),C=new Set(data.C.map(key));
   let c=0;
   for(const w of states)if(ps.every(([i,j])=>allowed(w,f,i,j))){c++;check(C.has(key(w)),'complete edge forces nested chain');}
   check(c===N,'N nested vertices');
   for(const [i,j] of ps){
     const delta=Math.abs(order.indexOf(i)-order.indexOf(j));
     const cyclic=delta===1||delta===N-1;
     const others=ps.filter(([k,l])=>!(k===i&&l===j));
     let extra=0,count=0;
     for(const w of states)if(others.every(([k,l])=>allowed(w,f,k,l))){
       count++;
       if(!C.has(key(w))){extra++;check(!allowed(w,f,i,j),'exceptional coordinate fails only freed edge');}
     }
     check(count===N+Number(cyclic) && extra===Number(cyclic),'exact one-edge allowed set');
   }
 }
}

// Fixed rational threshold law, pair isolation, and feasible transfers.
// Use integer counts of unit subintervals rather than floating probabilities.
for(let run=0;run<1200;run++){
 const N=3+gen(7),ps=pairs(N),d=61, f=[];
 while(f.length<N){const x=1+gen(d-1);if(!f.includes(x))f.push(x);}
 const {order,C}=phaseChain(f);
 const counts=new Map();
 for(let u=0;u<d;u++){
   const w=threshold(f,d,u),tag=key(w);
   counts.set(tag,(counts.get(tag)||0)+1);
 }
 for(const w of C)check(counts.has(key(w)),'chain positive probability at distinct phases');
 for(const [i,j] of ps){
   const f0=f[i]-f[j],lo=Math.floor(f0/d);let s=0,q=0;
   for(const w of C){
     const a=w[i]-w[j],c=counts.get(key(w));s+=c*a;q+=c*(a*d-f0)**2;
     check(a===lo||a===lo+1,'adjacent integer difference');
   }
   const r=mod(f0,d);
   check(s===f0,'edge mean');
   check(q===d*r*(d-r),'edge variance is the integer minimum');
 }
 const j=gen(N-1),i=order[j],l=order[j+1];
 const a=C[j].slice(),b=a.slice(),c=a.slice(),e=a.slice();
 b[i]=1;c[l]=1;e[i]=1;e[l]=1;
 const [A,B,G,E]=[a,b,c,e].map(norm);
 const tagA=key(A),tagB=key(B),tagG=key(G),tagE=key(E);
 check(counts.has(tagA)&&counts.has(tagB)&&counts.has(tagE)&&!counts.has(tagG),'first, middle, last and new vertex');
 const move=Math.min(counts.get(tagA),counts.get(tagE));
 const updated=new Map(counts);
 updated.set(tagA,updated.get(tagA)-move);
 updated.set(tagE,updated.get(tagE)-move);
 updated.set(tagB,updated.get(tagB)+move);
 updated.set(tagG,move);
 check(sum([...updated.values()])===d&&[...updated.values()].every(x=>x>=0),'maximal perturbation stays a probability law');
 for(const [k,h] of ps){
   const dd=w=>w[k]-w[h];
   const lin=dd(B)+dd(G)-dd(A)-dd(E);
   const quad=dd(B)**2+dd(G)**2-dd(A)**2-dd(E)**2;
   check(lin===0,'transfer keeps every directional mean');
   check(quad===(k===Math.min(i,l)&&h===Math.max(i,l)?2:0),'transfer covariance dual to one edge');
 }
}

// An exact compositional version of the two-gap integration.
function choose(n,k){
 if(n<k||k<0)return 0n;
 let ans=1n;for(let j=1;j<=k;j++)ans=ans*BigInt(n-j+1)/BigInt(j);
 return ans;
}
function compositions(n,k,f,p=[]){
 if(k===1){p.push(n);f(p);p.pop();return;}
 for(let j=1;j<=n-k+1;j++){p.push(j);compositions(n-j,k-1,f,p);p.pop();}
}
for(let N=3;N<=6;N++)for(let D=N;D<=N+9;D++){
  let count=0n,small=0n,large=0n;
  compositions(D,N,v=>{count++;small+=BigInt(Math.min(v[0],v[1]));large+=BigInt(Math.min(v[1],v[N-1]));});
  let predicted=0n;
  for(let k=0;k<=D;k++)predicted+=choose(D-1-2*k,N-1);
  check(count===choose(D-1,N-1)&&small===predicted&&small===large,'discrete Dirichlet two-gap formula');
}
function perms(a,f,s=0){
 if(s===a.length){f(a);return;}
 for(let j=s;j<a.length;j++){[a[s],a[j]]=[a[j],a[s]];perms(a,f,s+1);[a[s],a[j]]=[a[j],a[s]];}
}
for(let N=3;N<=8;N++){
 let count=0,c=0;
 perms(seq(N-1).map(x=>x+1),a=>{count++;if(a[0]===1||a[a.length-1]===1)c++;});
 check(c*(N-1)===2*count,'exact cyclic adjacency probability');
 const D=15000;let z=0n;
 for(let k=0;k<=D;k++)z+=choose(D-1-2*k,N-1);
 near(Number(z)/(D*Number(choose(D-1,N-1))),1/(2*N),6e-5,'simplex integral limit');
}

// Fractional parts after one common rotation: exact translation on toy grids.
for(const [N,d] of [[3,5],[4,7],[5,4]]){
 for(let u=0;u<d;u++){
   const all=new Set();
   visit(seq(d),N,t=>{all.add(key(t.map(x=>mod(x+u,d))));});
   check(all.size===d**N,'common shift preserves product Haar grid');
 }
}

// Sum-zero rounding via disjoint interval lengths with a common shifted grid.
for(let run=0;run<900;run++){
 const N=3+gen(12),d=77,f=Array.from({length:N-1},()=>gen(d));
 f.push(mod(-sum(f),d));
 const k=sum(f)/d, c=Array(N).fill(0);
 for(let u=0;u<d;u++){
   let head=0,hits=0;
   for(let i=0;i<N;i++){
      const foot=head+f[i];
      const r=mod(u-head,d);
      if(r<foot-head){hits++;c[i]++;}
      head=foot;
   }
   check(hits===k,'rounding preserves the sum constraint exactly');
 }
 check(key(c)===key(f),'simultaneous exact fractional marginals');
}

// Canonical trace Gram for prime cyclotomic powers, and normalization.
for(const p of [3,5,7,11,17,23]){
  for(let i=0;i<p;i++)for(let j=0;j<p;j++){
    const tr=sum(seq(p-1).map(k=>Math.cos(2*Math.PI*(k+1)*(i-j)/p)));
    near(tr,i===j?p-1:-1,2e-11,'all-embeddings power Gram');
  }
}
for(const N of [2,3])near(2*N/(N-1)*Math.pow(N,-2/(N-1)),1,1e-14,'low-dimensional normalized coincidence');
for(const N of [128,256,1024,2048,4096])near(2*N/(N-1)*Math.pow(N,-2/(N-1)),2,.15,'unit-covolume ratio tends to two');
console.log({exact_checks:exact,numerical_checks:numeric});
