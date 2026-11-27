
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

const scale=2520n;
const aa=[54n,-31n,-31n,4n,4n],bb=[54n,4n,4n,-31n,-31n];if(dot(aa,aa)!==4870n||dot(bb,bb)!==4870n||dot(aa,bb)!==2420n)throw Error('A4 witness');
for(let i=0;i<5;i++)for(let j=0;j<5;j++)for(const v of [aa,bb]){const w=v[i]-v[j];if((w>0n&&w*w>2435n)!==(i===0&&j!==0))throw Error('A4 blockers');}
for(const n of [7,8]){
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
  
  const cap=I.filter(i=>!U.some(r=>r[i]>0n));
  const rows=[...E,...U,...L,...cap.map(i=>E[i])], rhs=[...I.map(()=>0n),...U.map(()=>1n),...L.map(()=>1n),...cap.map(()=>2n)], out=new Map();
  function visit(set,start){
    if(set.length<n){
      for(let i=start;i<=rows.length-n+set.length;i++)visit([...set,i],i+1);
      return;
    }
    const a=set.map(i=>rows[i]),b=set.map(i=>rhs[i]);
    let d=det(a);if(!d)return;
    const N=I.map(j=>det(a.map((r,i)=>r.map((v,k)=>j===k?b[i]:v))));
    if(d<0n){d=-d;N.forEach((v,i)=>N[i]=-v);}
    if(N.some(v=>v<0n)||cap.some(i=>N[i]>2n*d)||U.some(r=>dot(r,N)>d)||L.some(r=>dot(r,N)<d))return;
    if(N.some(v=>scale*v%d))throw Error("rescale "+d+" rank "+n);
    const w=N.map(v=>scale*v/d);out.set(w.join(),w);
  }
  visit([],0);return [...out.values()];
}
const norm=k=>dot(k,adj.map(row=>dot(row,k)));





const ds=scale**2n*determinant,U=2n*ds,S=256n,gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));let levels=[[]],types=[];

function viable(C){
 if(!C.length)return true;const P=minimal(C),A=[...E,...P],b=A.map((_,i)=>BigInt(i>=n)),Q=A.map(r=>A.map(s=>dot(r,G.map(row=>dot(row,s)))));let ret=true;
 function go(J,i){if(!ret)return;if(J.length){const K=J.map(i=>J.map(j=>Q[i][j])),D=det(K);if(D>0n){const v=J.map(i=>b[i]),z=v.map((_,i)=>det(K.map((r,j)=>r.map((x,k)=>k===i?v[j]:x))));if(z.every(x=>x>=0n)&&dot(z,v)>=2n*D){ret=false;return;}}}if(J.length<n)for(let j=i;j<A.length;j++)go(J.concat([j]),j+1);}
 go([],0);return ret;
}
for(let k=0;k<=(n===7?27:29);k++){
 for(const L of levels){const C=L.map(i=>positive[i]);if(!viable(C))continue;const V=vertices(C),H=V.filter(v=>norm(v)>U),L0=V.filter(v=>norm(v)<=U),sum=I.map(j=>C.reduce((s,r)=>s+r[j],0n));
 
 let hull=[];
 if(!H.length)hull=V.filter(v=>norm(v)===U&&positive.filter(r=>dot(r,v)>scale).length===k&&!roots.some(r=>G.map(q=>dot(q,r)).every((t,i)=>t*scale===v[i]))).map(v=>v.map(x=>S*x));
 else{hull=H.map(h=>h.map(x=>x*S));for(const v of L0){const pt=(h,t)=>h.map((x,j)=>x*t+v[j]*(S-t));let low=0n,high=S;while(low+1n<high){const m=(low+high)>>1n;if(H.every(h=>norm(pt(h,m))<=U*S*S))low=m;else high=m;}for(const h of H)hull.push(pt(h,low));if(norm(v)===U)hull.push(v.map(x=>x*S));}}
 if(!hull.length)continue;const uniq=[...new Map(hull.map(h=>[h.join(),h])).values()];types.push({k,C:C.map(r=>index.get(r.join())),h:uniq});
 }const next=new Map();for(const L of levels)for(const r of maximal(positive.filter((_,i)=>!L.includes(i)))){const b=L.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(b.join(),b);}levels=[...next.values()];
}

if(levels.some(L=>viable(L.map(i=>positive[i]))))throw Error('upper blocker endpoint not certified');
let tests=0,ties=0;
for(const T of types){
 const C=T.C.map(i=>roots[i]),sum=I.map(k=>C.reduce((s,r)=>s+r[k],0n)),st=I.filter(i=>dot(G[i],sum)===0n);
 const orb=[],seen=new Set();for(const h of T.h){let k=h.join();if(!seen.has(k)){seen.add(k);orb.push(h);}}
 for(let i=0;i<orb.length;i++)for(const j of st){const u=orb[i],v=u.map((x,k)=>x-G[k][j]*u[j]),key=v.join();if(!seen.has(key)){seen.add(key);orb.push(v);}}
 const cs=new Set(T.C);
 function actual(h){const N=norm(h);return roots.every((r,i)=>{const a=dot(r,h);return (a>0n&&2n*determinant*a*a>N)===cs.has(i);});}
 const A=T.h.map(h=>({d:adj.map(r=>dot(r,h)),q:norm(h),inside:actual(h)}));
 for(const h of orb){const q=norm(h);if(q<=0n)throw Error('zero generator');let inside=null;for(const a of A){tests++;const z=dot(a.d,h);if(z<=0n||4n*z*z<a.q*q)throw Error('angular relaxation failed '+n+' '+T.k+' '+T.C.join());
  if(4n*z*z===a.q*q){ties++;if(a.inside){if(inside===null)inside=actual(h);if(inside)throw Error('realizable boundary equality');}}
 }}
}if(types.length!==(n===7?96:127)||Math.min(...types.map(t=>t.k))!==(n===7?6:8))throw Error('unexpected census');
if(tests!==(n===7?189326:290149)||ties!==(n===7?33:36))throw Error('comparison count');
console.log({rank:n,outerTypes:types.length,generatorComparisons:tests,boundaryEqualities:ties});
}
