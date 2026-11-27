'use strict';
// Exact 18-point ternary spectral-pair census. No data files or dependencies.
// --alternate changes the fiber split and every clique branch tie order.
const assert=require('node:assert/strict'),alt=process.argv.includes('--alternate');
const P=Array.from({length:81},(_,i)=>[i%3,Math.floor(i/3)%3,Math.floor(i/9)%3,Math.floor(i/27)]);
const H=P.slice(0,9).map(v=>v.slice(0,2));
const dot=(a,b)=>a.reduce((s,e,i)=>s+e*b[i],0)%3;
const num=v=>v[0]+3*v[1]+9*v[2]+27*v[3];
const sub=(a,b)=>num(a.map((x,i)=>(x+3-b[i])%3));
const reps=P.filter(v=>v.find(x=>x)!==undefined&&v.find(x=>x)===1);
assert.equal(reps.length,40);
const dmap=new Int16Array(81);
reps.forEach((v,i)=>{dmap[num(v)]=i;dmap[num(v.map(x=>2*x%3))]=i});
const D=P.map(v=>P.map(w=>dmap[sub(v,w)]));
const BITS=Array.from({length:81},(_,i)=>1n<<BigInt(alt?80-i:i));
const fieldIndex=new Map(BITS.map((v,i)=>[v,i]));
const ZA=reps.map(v=>v[2]===0&&v[3]===0);
const vdirs=[[1,0],[0,1],[1,1],[1,2]];
const anchors=[0,1,3],vars=alt?[2,6,8,4,5,7]:[2,4,5,6,7,8],power3=Array.from({length:9},(_,i)=>3**i);
const code=v=>v.reduce((m,x,i)=>m+power3[i]*(x%3),0);
function add(a,b){
 let u=0,p=1;
 for(let i=0;i<9;i++,p*=3){u+=p*((a%3+b%3)%3);a=(a/3)|0;b=(b/3)|0}
 return u;
}
const complementary=new Int32Array(19683);
for(let a=0;a<19683;a++){let b=a,c=0;for(let p of power3){c+=p*((3-b%3)%3);b=(b/3)|0}complementary[a]=c}
const choices=H.map(([a,b])=>H.flatMap(([x,y],i)=>H.slice(i+1).map(([s,t],j)=>{
 const e=[a,b,x,y],f=[a,b,s,t];
 return {i,j:j+i+1,loc:[num(e),num(f)],syn:code([x+s,y+t,x*x+s*s,x*y+s*t,y*y+t*t,a*(x+s),a*(y+t),b*(x+s),b*(y+t)]),
         counts:Uint16Array.from(reps,(v)=>(dot(e,v)===0?1:dot(e,v)===1?32:0)+(dot(f,v)===0?1:dot(f,v)===1?32:0))};
})));
function central(c,v){
 const i=v[0]+3*v[1],j=2*v[0]%3+3*(2*v[1]%3);
 return choices[c].find(p=>p.i===i&&p.j===j||p.i===j&&p.j===i);
}
function combine(c){
 const out=[];
 for(const a of choices[c[0]])for(const b of choices[c[1]])for(const f of choices[c[2]]){
  out.push({syn:add(add(a.syn,b.syn),f.syn),p:[a,b,f],c:Uint16Array.from(a.counts,(x,i)=>x+b.counts[i]+f.counts[i])});
 }return out;
}
const first=combine(vars.slice(0,3)),second=Array.from({length:19683},()=>[]);
for(const z of combine(vars.slice(3)))second[z.syn].push(z);
const bitCount=x=>{let n=0;while(x){x&=x-1n;n++}return n};
function has18(z){
 const adjacent=P.map((_,i)=>P.reduce((m,__,j)=>i!==j&&z[D[i][j]]?m|BITS[j]:m,0n));
 let nodes=0;
 function test(rem,h){
  nodes++;if(h===0)return true;
  if(bitCount(rem)<h)return false;
  // Greedy color bound on the remaining induced graph, then reverse branch.
  let set=rem,color=0,seq=[],col=[];
  while(set){
   color++;let whole=set;
   while(whole){
    const bit=whole&-whole,i=fieldIndex.get(bit);
    seq.push(bit);col.push(color);set^=bit;whole^=bit;whole&=~adjacent[i];
   }
  }
  for(let i=seq.length-1;i>=0;i--){
   if(col[i]<h)return false;
   const bit=seq[i];
   if(test(rem&adjacent[fieldIndex.get(bit)],h-1))return true;
   rem^=bit;
  }return false;
 }
 return [test(adjacent[0],17),nodes];
}
const normal=[[0,0,0],[0,0,1],[0,1,0],[0,1,1],[0,1,2]];
const a6=[0,1,3,9,27,80],b6=[0,66,73,34,17,50];
for(const [A,B] of [[a6,b6],[b6,a6]])for(let i=0;i<B.length;i++)for(let j=0;j<i;j++){
 const b=P[sub(P[B[i]],P[B[j]])],c=[0,0,0];for(let a of A)c[dot(P[a],b)]++;
 assert.deepEqual(c,[2,2,2]);
}
const count6=81*80*78*72*54/720;
assert.equal(count6,2729376);
console.log('6-point row/column checks: 30; size of the affine orbit:',count6);
const fixedCounts=[123180,113829,113829,113829,105306];
const fixedMasks=[115983,109203,109203,109203,103612];
for(const [caseId,typ] of normal.entries()){
 const a=anchors.map((c,i)=>central(c,vdirs[typ[i]]));
 assert(a.every(Boolean));
 const bsy=a.reduce((s,r)=>add(s,r.syn),0);
 const bco=Uint16Array.from(reps,(_,i)=>a[0].counts[i]+a[1].counts[i]+a[2].counts[i]);
 let candidates=0,passes=0,nodes=0,maxDirs=0;
 const tested=new Set();
 for(const s of first){
  const target=complementary[add(s.syn,bsy)];
  for(const t of second[target]){
   candidates++;
   const z=new Uint8Array(40);
   let nz=0,key=0;
   for(let j=0;j<40;j++){
    const v=(bco[j]+s.c[j]+t.c[j]===6+32*6);
    if(ZA[j])assert(v);
    if(v){z[j]=1;nz++;key+=2**j}
   }
   if(nz>maxDirs)maxDirs=nz;
   if(nz<9||tested.has(key))continue;
   tested.add(key);passes++;
   const [yes,n]=has18(z);nodes+=n;
   if(yes){
    console.log('SPECTRAL candidate',caseId,'A points',a.concat(s.p,t.p).flatMap(v=>v.loc),'zero bitmask',key);
    throw new Error('found');
   }
  }
 }
 assert.equal(candidates,fixedCounts[caseId]);assert.equal(passes,fixedMasks[caseId]);
 console.log('case',caseId,'candidates',candidates,'tested graphs',passes,'clique nodes',nodes,'max zero dirs',maxDirs);
}
