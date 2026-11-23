const shift=Number(process.argv[2]??5);
if(shift!==4&&shift!==5)throw Error('Pass return shift 4 or 5.');
const n=12,seq=Array.from({length:n},(_,i)=>i), mod=x=>(x+12)%12;
const l=i=>i^1,r=i=>mod(i+(i%2?1:-1)),a=12,z=13, mate=i=>i>=12?25-i:l(i);
const tags=[],v=new Map(),id=(i,j)=>i<j?14*i+j:14*j+i;
for(let i=0;i<14;i++)for(let j=i+1;j<14;j++)if(mate(i)!==j){v.set(id(i,j),tags.length);tags.push([i,j]);}
const bit=(i,j)=>1n<<BigInt(v.get(id(i,j)));
function candidates(i){
 const X=[i,mod(i+2),mod(i-2),mod(i+shift),mod(i-shift)],S=[z,...X],R=S.map(mate);
 const U=X.filter(x=>x!==i);
 const O=seq.filter(x=>!S.includes(x)&&!R.includes(x));
 const result=[];
 const rows=[];
 function match(A,B,s){
  if(!A.length){rows.push(s);return;}
  for(const q of B)if(q!==mate(A[0]))match(A.slice(1),B.filter(j=>j!==q),s.concat([[A[0],q]]));
 }
 match(S.filter(x=>x!==z&&x!==mod(i+shift)),R.filter(x=>x!==a&&x!==r(i)),[[z,r(i)],[mod(i+shift),a]]);
 for(const row of rows)for(let j=1;j<4;j++)for(let t=0;t<4;t++)for(let k=t+1;k<4;k++){
  const m=U.filter((_,s)=>s!==0&&s!==j);
  const add=[[U[0],U[j]],m,...U.map((x,p)=>[O[p===t||p===k?0:1],mate(x)])];
  const w=row.concat(add);
  result.push({w,mask:w.reduce((s,[p,q])=>s|bit(p,q),0n)});
 }
 return result;
}
function fit(i,j,x,y){const t=x&y;return r(i)===j?!t:!!t&&!(t&(t-1n))}
const E=seq.map(candidates);
const bits=E[0].map((_,k)=>1n<<BigInt(k)), ix=new Map(bits.map((b,i)=>[b,i]));
const masks=E.map(g=>(1n<<BigInt(g.length))-1n);
const compat=E.map((list,i)=>E.map((rs,j)=>i===j?null:list.map(q=>rs.reduce((s,b,k)=>fit(i,j,q.mask,b.mask)?s|bits[k]:s,0n))));

function count(x){let n=0;for(;x;x&=x-1n)n++;return n;}
function canonicalSubsets(target){
 const types=[];
 for(let mask=0;mask<4096;mask++){
  if(count(BigInt(mask))!==target)continue;
  let min=mask;
  for(let rot=2;rot<12;rot+=2){
   const m=((mask<<rot)|(mask>>(12-rot)))&4095;
   if(m<min)min=m;
  }
  if(min===mask)types.push(seq.filter(i=>mask>>i&1));
 }
 return types;
}
function solve(set){
 const dom=masks.slice();
 let visited=0;
 function tighten(d,queue){
  for(let k=0;k<queue.length;k++){
   const j=queue[k];
   for(const i of set)if(i!==j){
    let m=0n;
    for(let v=d[i];v;v&=v-1n){
     const b=v&-v;
     if(compat[i][j][ix.get(b)]&d[j])m|=b;
    }
    if(!m)return false;
    if(m!==d[i]){d[i]=m;queue.push(i);}
   }
  }
  return true;
 }
 function rec(d){
  visited++;
  let i=-1,k=199;
  for(const j of set){
   const q=count(d[j]);
   if(q>1&&q<k){i=j;k=q}
  }
  if(i===-1)return set.map(j=>[j,E[j][ix.get(d[j])].w]);
  for(let v=d[i];v;v&=v-1n){
   const m=v&-v,next=d.slice();next[i]=m;
   if(tighten(next,[i])){
    const out=rec(next);if(out)return out;
   }
  }
  return null;
 }
 const solution=tighten(dom,set.slice())?rec(dom):null;
 return {visited,solution};
}
const sets=canonicalSubsets(9);
let checked=0, nodes=0, witness=null;
for(const set of sets){
 const d=solve(set);checked++;nodes+=d.visited;
 if(d.solution){witness=d.solution;break;}
}
const measured=[sets.length,checked,nodes,Boolean(witness)];
const expected=shift===5?[38,38,4192,false]:[38,25,6086,true];
if(JSON.stringify(measured)!==JSON.stringify(expected))throw Error(JSON.stringify(measured));
console.log(JSON.stringify({shift,measured,witness}));
