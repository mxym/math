let geom;
'use strict';
// Run with Node.js. Fundamental chamber coordinates are simple-root inner products.



function dot(a, b) {
  return a.reduce((sum,v,i)=>sum+v*b[i],0n);
}

// Fraction-free determinant with exact row pivoting.
function det(rows) {
  const a=rows.map(row=>row.slice());
  let sign=1n, prev=1n;
  for(let j=0;j<a.length-1;j++){
    const pivot=a.findIndex((row,i)=>i>=j&&row[j]!==0n);
    if(pivot<0)return 0n;
    if(pivot!==j){[a[j],a[pivot]]=[a[pivot],a[j]];sign=-sign;}
    for(let i=j+1;i<a.length;i++)for(let k=j+1;k<a.length;k++){
      const num=a[i][k]*a[j][j]-a[i][j]*a[j][k];
      if(num%prev!==0n)throw Error('division');
      a[i][k]=num/prev;
    }
    for(let i=j+1;i<a.length;i++)a[i][j]=0n;
    prev=a[j][j];
  }
  return sign*a.at(-1).at(-1);
}

const assert=require('node:assert/strict'), scale=2520n;
for(const n of [7]){
const I=Array.from({length:n},(_,i)=>i);
const E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:
  (i<n-1&&j<n-1&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===n-1)?-1n:0n));
const determinant=det(G);
const adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const roots=E.map(r=>r.slice()), index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){
  const r=reflect(roots[j],i);
  if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r);}
}
if(roots.length!==[72,126,240][n-6])throw Error("root count");
const positive=roots.filter(r=>r.every(v=>v>=0n));
const maximal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v>=r[i])));
const minimal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v<=r[i])));

function vertices(C){
  const U=maximal(positive.filter(r=>!C.includes(r))), L=minimal(C);
  
  if(I.some(i=>!U.some(r=>r[i]>0n)))throw Error('unbounded chamber coordinate');
  const rows=[...E,...U,...L], rhs=[...I.map(()=>0n),...U.map(()=>1n),...L.map(()=>1n)], out=new Map();
  function visit(set,start){
    if(set.length<n){
      for(let i=start;i<=rows.length-n+set.length;i++)visit([...set,i],i+1);
      return;
    }
    const a=set.map(i=>rows[i]),b=set.map(i=>rhs[i]);
    let d=det(a);if(!d)return;
    const N=I.map(j=>det(a.map((r,i)=>r.map((v,k)=>j===k?b[i]:v))));
    if(d<0n){d=-d;N.forEach((v,i)=>N[i]=-v);}
    if(N.some(v=>v<0n)||U.some(r=>dot(r,N)>d)||L.some(r=>dot(r,N)<d))return;
    if(N.some(v=>scale*v%d))throw Error("rescale");
    const w=N.map(v=>scale*v/d);out.set(w.join(),w);
  }
  visit([],0);return [...out.values()];
}
const norm=k=>dot(k,adj.map(row=>dot(row,k)));




const ds=scale*scale*determinant,Q=(a,b)=>dot(a,G.map(row=>dot(row,b))),rg=v=>G.map(row=>dot(row,v));let levels=[[]],C7=null,V7=null,R8=null;
const hist=[];
for(let k=0;k<=12;k++){const H={};let ok=0;
 for(const a of levels){const C=a.map(i=>positive[i]),V=vertices(C),N=V.map(norm),M=N.reduce((a,b)=>a>b?a:b);
   if(M<2n*ds)continue;
   if(M===2n*ds&&!V.some(v=>norm(v)===2n*ds&&positive.filter(r=>dot(r,v)>scale).length===k&&!roots.some(r=>rg(r).every((x,i)=>x*scale===v[i]))))continue;
   ok++;const ws=C.map(r=>{const d=C.map(t=>Q(r,t));assert(d.every(z=>z>=0n));return 2*d.filter(x=>x===1n).length+d.filter(x=>x===0n).length;});
   for(const w of ws)H[w]=(H[w]||0)+1;
   if(k===7){assert(!C7);assert(ws.every(w=>w===12));C7=C.map(r=>index.get(r.join()));V7=V.map(v=>v.map(x=>{assert.equal(12n*x%scale,0n);return Number(12n*x/scale);}));}
   for(const [j,w] of ws.entries())if(w<=11){if(w===10){assert.equal(k,6);assert(ws.every(t=>t===10));}else{assert.equal(w,11);assert.equal(k,8);assert(!R8);R8={ids:C.map(t=>index.get(t.join())),r:index.get(C[j].join())};}}
 }hist.push([k,levels.length,ok,Math.min(...Object.keys(H).map(Number))]);
 const next=new Map();for(const a of levels)for(const r of maximal(positive.filter((_,i)=>!a.includes(i)))){const b=a.concat([positive.indexOf(r)]).sort((x,y)=>x-y);next.set(b.join(),b);}levels=[...next.values()];
}assert(C7&&R8);assert(hist.slice(0,6).every(z=>!z[2]));console.log('small chamber classes',hist.map(t=>t.slice(0,3)));geom={C7,V7,R8,rootKeys:roots.map(r=>r.join())};
}
'use strict';
const summary = (() => {


function dot(a, b) {
  return a.reduce((sum,v,i)=>sum+v*b[i],0n);
}

// Fraction-free determinant with exact row pivoting.
function det(rows) {
  const a=rows.map(row=>row.slice());
  let sign=1n, prev=1n;
  for(let j=0;j<a.length-1;j++){
    const pivot=a.findIndex((row,i)=>i>=j&&row[j]!==0n);
    if(pivot<0)return 0n;
    if(pivot!==j){[a[j],a[pivot]]=[a[pivot],a[j]];sign=-sign;}
    for(let i=j+1;i<a.length;i++)for(let k=j+1;k<a.length;k++){
      const num=a[i][k]*a[j][j]-a[i][j]*a[j][k];
      if(num%prev!==0n)throw Error('division');
      a[i][k]=num/prev;
    }
    for(let i=j+1;i<a.length;i++)a[i][j]=0n;
    prev=a[j][j];
  }
  return sign*a.at(-1).at(-1);
}

const n=7,I=Array.from({length:n},(_,i)=>i),E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:((i<6&&j<6&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===6))?-1n:0n));
const roots=E.slice(),index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){const r=reflect(roots[j],i);if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r)}}
const C=roots.flatMap((r,i)=>r[5]+r[6]>2n?[i]:[]);
const neg=roots.map(r=>index.get(r.map(v=>-v).join()));
const mask=xs=>xs.reduce((m,i)=>m|(1n<<BigInt(i)),0n);
const perm=I.map(i=>roots.map(r=>index.get(reflect(r,i).join())));

const D=det(G), adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const base=adj.map(r=>r[5]+r[6]), q=[base], seen=new Set(q.map(v=>v.join()));
for(let i=0;i<q.length;i++)for(const k of I){const p=reflect(q[i],k),key=p.join();if(!seen.has(key)){seen.add(key);q.push(p);}}
const g0=G.map(r=>dot(r,base)), gdot=(p,r)=>dot(G.map(row=>dot(row,p)),r);
const orbit=q.map(v=>({v,b:mask(roots.flatMap((r,i)=>gdot(v,r)>2n*D?[i]:[]))}));
if(roots.length!==126 || C.length!==6 || dot(g0,base)!==8n*D*D)throw Error('E7 witness norm');
const baseMask=mask(C), axes=mask([...C,...C.map(i=>neg[i])]);

if(roots.some((r,i)=>r.join()!==geom.rootKeys[i]))throw Error('coordinate mismatch');const C7=geom.C7;
const seven=[C7],sm=new Set([mask(C7)]);for(let j=0;j<seven.length;j++)for(const p of perm){const S=seven[j].map(i=>p[i]),k=mask(S);if(!sm.has(k)){sm.add(k);seven.push(S);}}
if(seven.length!==576)throw Error('E7 seven sets');
const gram=(a,b)=>Number(dot(a,b)), W=orbit.map(o=>({v:o.v.map(Number),g:G.map(row=>Number(dot(row,o.v))),b:o.b,k:6})),H=seven.map(ids=>({ids,b:mask(ids),k:7})), ng=roots.map(r=>r.map(Number)),dd=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
const vT=geom.V7,gram7=vT.map(v=>C7.map(i=>dd(ng[i],v)).sort((a,b)=>b-a)),ds=Number(D);
if([ng,gram7,W.map(x=>x.g),W.map(x=>x.v)].some(T=>T.some(row=>row.some(t=>!Number.isSafeInteger(t)||Math.abs(t)>1000))))throw Error('integer dot range');
// With dimension 7 the largest expression below is bounded by 10^12.
function mix(a,b){const x=b.ids.map(i=>dd(a.g,ng[i])).sort((a,b)=>a-b);let min=1e20;for(const y of gram7){const v=8*dd(x,y)-x.reduce((s,z)=>s+z,0)*y.reduce((s,z)=>s+z,0);min=Math.min(min,v);}return min;}
function nn(a,b){if(a.k>b.k)[a,b]=[b,a];if(a.k===7)return false;if(a.b&b.b)return false;return a.k===b.k?dd(a.g,b.v)<-4*ds*ds:mix(a,b)<-8*12*2*ds;}
const M=new Set(),b0=W[0],axis0=axes;for(const y of W.concat(H)){if(y.b&axis0||!nn(b0,y))continue;const U=b0.b|y.b;if(y.k===7){M.add(U);continue;}
 const ids=roots.map((_,i)=>i).filter(i=>U>>BigInt(i)&1n),aa=mask(ids.concat(ids.map(i=>neg[i])));for(let i=0;i<126;i++)if(!(aa>>BigInt(i)&1n))M.add(U|1n<<BigInt(i));}
if(q.length!==4032||new Set(W.map(v=>v.b)).size!==4032||M.size!==2040||W.filter(y=>!(y.b&axes)&&nn(b0,y)).length!==20||H.filter(y=>!(y.b&axes)&&nn(b0,y)).length!==20)throw Error('anchored census');let kept=[],maxV=0;for(const U of M){const V=W.concat(H,H).filter(z=>(z.b&U)===z.b),edges=[];maxV=Math.max(maxV,V.length);for(let i=0;i<V.length;i++)for(let j=0;j<i;j++)if(nn(V[i],V[j]))edges.push([i,j]);
 let ok=false;outer:for(const [i,j] of edges)for(const [x,y] of edges){if(i===x||i===y||j===x||j===y)continue;ok=true;break outer;}
 if(ok)kept.push([U.toString(),V.map(z=>z.k),edges]);}if(kept.length||maxV!==10)throw Error('disjoint negative edges');console.log('full-axis: 2040 deletion sets, zero disjoint possible negative edges');
{const gram=(r,s)=>dot(r,G.map(row=>dot(row,s))),ids=geom.R8.ids,p=perm,r=geom.R8.r,nr=neg[r],orth=mask(roots.map((s,i)=>gram(s,roots[r])===0n?i:-1).filter(i=>i>=0));
const queue=[[ids,r]],recorded=new Set([mask(ids)]),Z=mask(ids)&orth;let hit=0,zs=[];for(let i=0;i<queue.length;i++){const [v,k]=queue[i];if(k===nr&&(mask(v)&orth)===Z){hit++;if(hit<6)zs.push(v);}
for(const g of p){const a=v.map(i=>g[i]),m=mask(a);if(recorded.has(m))continue;recorded.add(m);queue.push([a,g[k]]);}}if(queue.length!==20160||hit!==1)throw Error('opposite eight-pattern census');const lost=mask(ids.concat(zs[0])),pop=x=>{let n=0;while(x){x&=x-1n;n++;}return n;};const sections=roots.map(t=>mask(roots.map((s,i)=>gram(t,s)===0n?i:-1).filter(i=>i>=0)));if(!sections.every(m=>pop(m)===60)||Math.min(...sections.map(m=>pop(m&lost)))!==2)throw Error('D6 section');console.log('opposite case: unique eight/eight union, at least 58 D6 roots retained');}
})();
