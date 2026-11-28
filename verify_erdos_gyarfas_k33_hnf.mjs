// Bit-set replay for the fixed K3,3 base.
// node verify_erdos_gyarfas_k33_hnf.mjs MIN MAX
// Output rows: index, total HNFs, candidates after the unconditional
// short-cycle tests, and candidates after all 16-cycle tests.
function cycleOracles(){
const adj=[[3,4,5],[3,4,5],[3,4,5],[0,1,2],[0,1,2],[0,1,2]];
const moves=Array.from({length:6},()=>Array(6).fill(-1));
moves[1][4]=0;moves[1][5]=1;moves[2][4]=2;moves[2][5]=3;
function vector(path){
const acc=[0,0,0,0];
for(let k=1;k<path.length;k++){
 const from=path[k-1], to=path[k], i=from<3?moves[from][to]:moves[to][from];
 if(i!==-1)acc[i]+=from<3?1:-1;
}
return acc;
}
function canon(v){
 const first=v.find(x=>x!==0);
 return first<0?v.map(x=>-x):v;
}
function wordForms(len){
 const forms=new Map();
 for(let start=0;start<3;start++){
  const path=[start];
  function dfs(cur,left){
   if(left===0){
    if(cur!==start||path[1]===path.at(-2))return;
    const v=canon(vector(path));forms.set(v.join(","),v);return;
   }
   for(const next of adj[cur]) if(next!==path.at(-2)&&(left!==1||next===start)){
    path.push(next);dfs(next,left-1);path.pop();
   }
  }
  dfs(start,len);
 }
 return [...forms.values()].sort((a,b)=>a.reduce((s,v)=>s+Math.abs(v),0)-b.reduce((s,v)=>s+Math.abs(v),0));
}
function makeClause(path){
 const target=vector(path);
 const blockers=new Map();
 for(let i=0;i<path.length-1;i++)for(let j=i+1;j<path.length-1;j++){
  if(path[i]!==path[j])continue;
  const v=canon(vector(path.slice(i,j+1)));blockers.set(v.join(","),v);
 }
 return {target,blockers:[...blockers.values()],path};
}
function all16(){
 const known=new Set([...wordForms(4),...wordForms(8)].map(v=>v.join(",")));
 const examples=new Map();
 for(let start=0;start<3;start++){
  const path=[start];
  function dfs(cur,left){
   if(left===0){
    if(cur!==start||path[1]===path.at(-2))return;
    const target=canon(vector(path)), key=target.join(",");
    if(known.has(key))return;
    const prior=examples.get(key)??[];
    if(prior.some(x=>x.blocks.length===0))return;
    const found=new Set();
    for(let i=0;i<path.length-1;i++)for(let j=i+1;j<path.length-1;j++){
     if(path[i]!==path[j])continue;
     const block=canon(vector(path.slice(i,j+1)));
     if([-2,-1,0,1,2].some(h=>block.every((x,i)=>x===h*target[i])))return;
     if(![-2,-1,0,1,2].some(h=>known.has(canon(block.map((x,i)=>x+h*target[i])).join(","))))found.add(block.join(","));
    }
    const blocks=[...found];
    if(prior.some(p=>p.blocks.every(x=>found.has(x))))return;
    examples.set(key,[...prior.filter(p=>!blocks.every(x=>p.blocks.includes(x))),{blocks,path:path.slice()}]);
    return;
   }
   for(const next of adj[cur]) if(next!==path.at(-2)&&(left!==1||next===start)){
    path.push(next);dfs(next,left-1);path.pop();
   }
  }
  dfs(start,16);
 }
 return [...examples.values()].flat();
}
return {wordForms,makeClause,all16};
}
const certificates=cycleOracles().all16();
const cc=Array.from({length:16},(_,n)=>certificates.filter(c=>c.blocks.length===n).length);if(cc.reduce((a,b)=>a+b,0)!==certificates.length||cc[0]!==501||cc[1]!==126||cc.slice(2).some(x=>x))throw Error('multi-block truncation');
console.log('clause histogram',cc);
function bitScan(low,high){
 const {wordForms,makeClause}=cycleOracles();
 const tc=wordForms(4), te=wordForms(8);
 const pure=[...new Map([...tc,...te].map(t=>[t.join(","),t])).values()];
 const cond=[];
 for(const {path,blocks} of certificates){
  const t=makeClause(path).target;
  if(blocks.length)cond.push([t,blocks[0].split(",").map(Number)]);
  else pure.push(t);
 }
 const out=[];
 for(let n=low;n<=high;n++){
  let count=0, gap=0, survivors=0;
  for(let a=1;a<=n;a++)if(n%a===0){
   const K=Math.ceil(a/32);
   const byCoefficient=new Map();
   function mask(t){
    if(byCoefficient.has(t))return byCoefficient.get(t);
    const v=new Uint32Array(K*a);
    for(let w=0;w<a;w++){
     const r=(t*w)%a, k=r<0?r+a:r;
     v[K*k+(w>>5)]|=1<<(w&31);
    }
    byCoefficient.set(t,v);
    return v;
   }
   const allLast=(a%32===0?0xffffffff:2**(a%32)-1)|0;
   for(let b=1;a*b<=n;b++)if(n%(a*b)===0)
   for(let c=1;a*b*c<=n;c++)if(n%(a*b*c)===0){
    const d=n/(a*b*c);
    count+=a**3*b**2*c;
    for(let x=0;x<b;x++)for(let y=0;y<b;y++)for(let z=0;z<c;z++){
     function reduce(t){
      if(t[3]%d)return null;
      const D=t[3]/d, y2=t[2]-z*D;
      if(y2%c)return null;
      const C=y2/c, y1=t[1]-x*C-y*D;
      if(y1%b)return null;
      return [t[0],y1/b,C,D];
     }
     const fixed=[],move=[],conditionally=[];
     for(const t of pure){
      const R=reduce(t);if(!R)continue;
      if(R[3]%a===0) fixed.push(R);
      else move.push([R,mask(R[3])]);
     }
     for(const [t,s] of cond){
      const T=reduce(t);
      if(T)conditionally.push([T,reduce(s)]);
     }
     const bits=new Int32Array(K);
     for(let u=0;u<a;u++)for(let v=0;v<a;v++){
      let bad=false;
      for(let i=0;i<fixed.length;i++){
       const q=fixed[i];
       if((q[0]-q[1]*u-q[2]*v)%a===0){bad=true;break;}
      }
      if(bad)continue;
      bits.fill(0);
      for(let i=0;i<move.length;i++){
       const [q,table]=move[i],r=(q[0]-q[1]*u-q[2]*v)%a,pos=K*(r<0?r+a:r);
       let full=true;
       for(let j=0;j<K;j++){
        bits[j]|=table[pos+j];
        if(bits[j] !== (j===K-1?allLast:-1))full=false;
       }
       if(full){bad=true;break;}
      }
      if(bad)continue;
      for(let w=0;w<a;w++){
       if(bits[w>>5]&(1<<(w&31)))continue;
       gap++;
       const member=q=>(q[0]-q[1]*u-q[2]*v-q[3]*w)%a===0;
       if(!conditionally.some(([t,s])=>member(t)&&(!s||!member(s))))survivors++;
      }
     }
    }
   }
  }
  out.push([n,count,gap,survivors]);
  console.log([n,count,gap,survivors].join(','));
 }
 return out;
}

function independentCount(n){
 let answer=1;
 for(let p=2;p<=n;p++){
  if(n%p)continue;
  let e=0;
  while(n%p===0){n/=p;e++}
  const h=Array(e+1).fill(0);h[0]=1;
  for(let j=0;j<4;j++)for(let i=1;i<=e;i++)h[i]+=p**j*h[i-1];
  answer*=h[e];
 }
 return answer;
}

const min=Number(process.argv[2]??1);
const max=Number(process.argv[3]??133);
if(!Number.isSafeInteger(min)||!Number.isSafeInteger(max)||min<1||max<min||max>133)
 throw Error("Use an inclusive index range in 1..133");
const out=bitScan(min,max);
for(const [n,count,gap,survivors] of out){
 if(count!==independentCount(n)||survivors!==(n===133?56:0))
  throw Error("Unexpected census row: "+[n,count,gap,survivors]);
}
if(min===1&&max===133&&out.slice(0,-1).reduce((s,r)=>s+r[1],0)!==166344289)
 throw Error("Cumulative count mismatch");
console.log("PASS",min,max,out.reduce((s,r)=>s+r[1],0));
