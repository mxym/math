"use strict";

// Phase I: exact moved-pair supports and sign blocks. Output JSON for phase II.

function pc(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return ((((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24);}
function parityPatterns(n,degree,cap=Infinity){const H=n/2,all=(1<<n)-1,rows=new Int32Array(n),sig=(v)=>+(v>=H),counts=Array(n+1).fill(0),out=[];let done=0;
function dfs(mask,depth){
 counts[depth]++;if(depth===n){done++;out.push(Array.from(rows));return done>=cap;}
 let v=-1,min=1e9,mp=new Map;
 for(let b=all^mask;b;b&=b-1){const i=31-Math.clz32(b&-b),deg=pc(rows[i]&mask),prio= -(deg*4)+(i>=H?0:1);
    if(prio<min){min=prio;v=i;}
 }
 if(v<0)throw Error("unassigned");
 const bits=(all^mask)^(1<<v),need=degree-pc(rows[v]&mask);
 if(need<0||need>pc(bits))return false;
 for(let b=bits;b;b&=b-1){const i=31-Math.clz32(b&-b),key=(rows[i]&mask)+(sig(i)<<n);if(pc(rows[i]&mask)>=degree)continue;mp.set(key,(mp.get(key)||0)|(1<<i));}
 const groups=Array.from(mp.values());
 function enumRows(g,k,nb){
  if(g===groups.length){if(k!==0)return false;const row=(rows[v]&mask)|nb;
   for(let b=mask;b;b&=b-1){const i=31-Math.clz32(b&-b),same=sig(i)===sig(v),adj=!!(row>>i&1);
      if((pc(row&rows[i])&1)!==+(same&&!adj))return false;}
   const saved=rows[v];rows[v]=row;
   for(let b=nb;b;b&=b-1){const i=31-Math.clz32(b&-b);rows[i]|=1<<v;}
   const stop=dfs(mask|(1<<v),depth+1);
   for(let b=nb;b;b&=b-1){const i=31-Math.clz32(b&-b);rows[i]^=1<<v;}
   rows[v]=saved;return stop;
  }
  let z=groups[g],s=nb;
  if(enumRows(g+1,k,s))return true;
  for(let i=1;z&&i<=k;i++){s|=z&-z;z&=z-1;if(enumRows(g+1,k-i,s))return true;}
  return false;
 }
 return enumRows(0,need,0);
}
dfs(0,0);return{n,degree,counts,done,out};}

function signs(F,cap=Infinity){const n=F.length,all=(1<<n)-1,diag=i=>i<n/2?1:-1,R=F.map((x,i)=>all^x^(1<<i)),plus=new Int32Array(n),tree=new Int32Array(n);const todo=[0];let known=1;
for(let k=0;k<todo.length;k++){const v=todo[k];for(let b=R[v]&~known;b;b&=b-1){const i=31-Math.clz32(b&-b);known|=1<<i;tree[v]|=1<<i;tree[i]|=1<<v;todo.push(i);}}
if(known!==all)throw Error("split disconnected");
const stats=Array(n+1).fill(0),out=[];
function dfs(mask,k){
 stats[k]++;if(k===n){out.push(Array.from(plus));return out.length>=cap;}
 let v=-1,best=100;
 for(let b=all^mask;b;b&=b-1){const i=31-Math.clz32(b&-b),z=pc(R[i]&~(tree[i]|mask));if(z<best){v=i;best=z;}}
 const U=R[v]&~(tree[v]|mask),must=(plus[v]&mask)|tree[v],saved=plus[v],others=[];
 for(let b=mask;b;b&=b-1){const i=31-Math.clz32(b&-b),inter=R[v]&R[i],sign=(R[v]>>i&1)?((must>>i&1)?1:-1):0,rhs=-(diag(i)+diag(v))*sign/2;
  const diff=(pc(inter)-rhs)/2;
  if(diff%1||diff<0)return false;
  others.push([inter,plus[i],diff]);
 }
 for(let s=U;;s=(s-1)&U){
  const chosen=must|s;if(others.every(([u,y,d])=>pc(u&(y^chosen))===d)){
   plus[v]=chosen;
   const fresh=chosen&~mask;
   for(let b=fresh;b;b&=b-1)plus[31-Math.clz32(b&-b)]|=1<<v;
   const stop=dfs(mask|(1<<v),k+1);
   for(let b=fresh;b;b&=b-1)plus[31-Math.clz32(b&-b)]^=1<<v;
   plus[v]=saved;if(stop)return true;
  }
  if(s===0)break;
 }
 return false;
}
dfs(0,0);return {stats,out};}

function sparsePlus(F){const n=F.length,all=(1<<n)-1,tree=new Set,seen=new Set([0]);for(const i of seen) for(let b=F[i];b;b&=b-1){const j=31-Math.clz32(b&-b);if(!seen.has(j)){seen.add(j);tree.add(n*Math.min(i,j)+Math.max(i,j));}}
const fringe=[],base=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?(i<n/2?1:-1):(tree.has(n*Math.min(i,j)+Math.max(i,j))?2:0)));
for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if((F[i]>>j&1)&&!tree.has(n*i+j))fringe.push([i,j]);
if(seen.size!==n||fringe.length!==17)throw Error("pair support/tree");
function sing(U,p,r){const A=U.map((R,i)=>R.map((z,j)=>(z+(i===j?-r:0)+p)%p));const inv=Array(p).fill(0);for(let i=1;i<p;i++)for(let j=1;j<p;j++)if(i*j%p===1)inv[i]=j;
 for(let col=0;col<n;col++){let j=col;while(j<n&&A[j][col]===0)j++;if(j===n)return true;[A[j],A[col]]=[A[col],A[j]];
   for(let i=col+1;i<n;i++)if(A[i][col]){const c=A[i][col]*inv[A[col][col]]%p;for(let k=col+1;k<n;k++)A[i][k]=(A[i][k]+p*p-c*A[col][k])%p;}
 }return false;
}
const primes=[11,19,31,41,59,61,71,79,89,101,109,131];
const checks=primes.map(p=>[p,Array.from({length:p/2},(_,i)=>i).find(i=>(i*i-45)%p===0)]).filter(x=>x[1]!==undefined);
const reject=Array(checks.length).fill(0),survivors=[];
for(let m=0;m<(1<<fringe.length);m++){
 fringe.forEach(([i,j],k)=>base[i][j]=base[j][i]=(m>>k&1)?2:-2);
 let ok=true;for(let j=0;j<checks.length;j++){const [p,r]=checks[j];if(!sing(base,p,r)||!sing(base,p,p-r)){reject[j]++;ok=false;break;}}
 if(ok)survivors.push([m,base.map(row=>row.slice())]);
}return {n,fringe:fringe.length,checks,reject,survivors};}

const assert=require("node:assert/strict");
const par=parityPatterns(16,4);
assert.deepEqual(par.counts,[1,5,34,196,707,1785,2547,2107,1303,495,333,123,59,14,7,1,1]);
assert.equal(par.done,1);
const F=par.out[0],sigma=i=>i<8?1:-1;
assert.deepEqual(F,[3336,20752,41248,12801,34306,18948,25728,38976,519,312,4177,8353,1162,2124,32866,16532]);
for(let i=0;i<16;i++)for(let j=0;j<16;j++){
 assert.equal((F[i]>>j)&1,(F[j]>>i)&1);
 if(i===j)assert.ok(pc(F[i])===4&&!(F[i]>>i&1)); 
 else assert.equal(pc(F[i]&F[j])%2,+(sigma(i)===sigma(j)&&!(F[i]>>j&1)));
}
const anti=signs(F).out;
assert.equal(anti.length,35);
for(const R of anti){
 const b=(i,j)=>i===j?sigma(i):(F[i]>>j&1)?0:(R[i]>>j&1)?2:-2;
 for(let i=0;i<16;i++)for(let j=0;j<16;j++){
  assert.equal(b(i,j),b(j,i));
  assert.equal(Array.from({length:16},(_,k)=>b(i,k)*b(k,j)).reduce((a,c)=>a+c,0),i===j?45:0);
 }
}
const p=sparsePlus(F);
assert.deepEqual(p.checks,[[11,1],[19,8],[31,13],[41,2],[59,24],[61,17],[71,20],[79,19],[89,32],[101,34],[109,46],[131,62]]);
assert.deepEqual(p.reject,[128713,2244,54,0,0,0,0,0,0,0,0,0]);
assert.equal(p.survivors.length,61);
console.log(JSON.stringify({F,anti,plus:p.survivors}));
