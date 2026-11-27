'use strict';
// Integer certificate for degree-six moment rigidity and no two layered normals.
const p=13, mod=x=>(x%p+p)%p;
const inv=Array.from({length:p},(_,i)=>Array.from({length:p},(_,x)=>x).find(j=>mod(i*j)===1));
const check=(q,s)=>{if(!q)throw Error(s);};
const t=[[0,0],[1,0],[0,1]];
for(let x=0;x<p;x++)for(let y=0;y<p;y++){
  if(t.some(([u,v])=>x===u&&y===v))continue;
  check(!t.every(([u,v])=>x===u||y===v||mod(x+y-u-v)===0),'fourth point with 3 directions');
}
const V=[];
for(let y=0;y<p;y++)for(let z=0;z<p;z++)V.push([1,y,z]);
for(let z=0;z<p;z++)V.push([0,1,z]);
V.push([0,0,1]);
const lines=V.map(a=>V.flatMap((x,i)=>mod(a.reduce((s,v,j)=>s+v*x[j],0))===0?[i]:[]));
const bits=lines.map(l=>l.reduce((x,i)=>x|1n<<BigInt(i),0n));
const base=[0,169,182],cand=V.map((_,i)=>i).filter(i=>!base.includes(i)),bb=base.reduce((x,i)=>x|bits[i],0n);
const atLeast4=x=>{for(let i=0;i<4;i++){if(!x)return false;x&=x-1n;}return true;};
const stats={};
for(let i=0;i<cand.length;i++)for(let j=i+1;j<cand.length;j++)for(let k=j+1;k<cand.length;k++){
  const [a,b,c]=[cand[i],cand[j],cand[k]], mask=bb|bits[a]|bits[b]|bits[c];
  if(!bits.every(l=>atLeast4(l&mask)))continue;
  const S=base.concat(a,b,c),mult=new Uint8Array(V.length);
  for(let l of S)for(let x of lines[l])mult[x]++;
  if(mult.some(v=>v>3))continue;
  const four=Uint8Array.from(lines,l=>Number(l.reduce((s,x)=>s+(mult[x]>0),0)===4));
  // By symmetric dot-product incidence, lines[x] are precisely the lines through x.
  const key=S.map(l=>lines[l].filter(x=>mult[x]===1&&!lines[x].some(k=>four[k])).length).sort((u,v)=>u-v).join(',');
  stats[key]=(stats[key]??0)+1;
}
check(Object.keys(stats).length===2&&stats['0,0,0,0,0,0']===576&&stats['0,0,1,1,1,2']===17280,'six-factor census');
console.log(stats);
const cs=[],seen=new Set();
function subsets(i,n,xs){
  if(n){for(let j=i;j<=p-n;j++)subsets(j+1,n-1,xs.concat(j));return;}
  if(seen.has(xs.join(',')))return;
  cs.push(xs);
  for(let s=1;s<p;s++)for(let d=0;d<p;d++)seen.add(xs.map(x=>mod(s*x+d)).sort((u,v)=>u-v).join(','));
}
subsets(0,5,[]);check(cs.length===10,'affine orbit count');
const lambda=A=>A.map(x=>inv[A.filter(y=>y!==x).reduce((u,y)=>mod(u*(x-y)),1)]);
let cases=0,valid=0;
for(let X of cs)for(let Y of cs){
  const lx=lambda(X),ly=lambda(Y);
  for(let a=0;a<p;a++)for(let b=0;b<p;b++)for(let c=0;c<p;c++){
    cases++;
    const g=X.map((x,i)=>Y.map((y,j)=>mod(lx[i]*ly[j]*(a+b*x+c*y))));
    if(g.every(row=>row.every(v=>v<=5)&&row.reduce((s,v)=>s+v,0)===13)&&Y.every((_,j)=>g.reduce((s,row)=>s+row[j],0)===13))valid++;
  }
}
check(!valid&&cases===219700,'layered grid census');console.log({affineOrbits:cs.length,cases,valid});
