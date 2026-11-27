
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

const job=process.argv[2]||'core',width=job==='core'?13:Number(process.argv[3]);if(!['core','signed'].includes(job)||!Number.isInteger(width)||width<13||width>17)throw Error('Use core or signed 14..17');
const scale=2520n;
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





const ds=scale**2n*determinant,U=2n*ds,S=256n,gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));let levels=[[]],types=[],seed=[],formal=[];
for(let k=0;k<=width;k++){
 for(const L of levels){const C=L.map(i=>positive[i]);const f={k,C:C.map(r=>index.get(r.join())),v:null,ch:[]};formal.push(f);const V=vertices(C),H=V.filter(v=>norm(v)>U),L0=V.filter(v=>norm(v)<=U),sum=I.map(j=>C.reduce((s,r)=>s+r[j],0n));
 if(k===6)seed.push(C.map(r=>index.get(r.join())));
 let hull=[];
 if(!H.length)hull=V.filter(v=>norm(v)===U&&positive.filter(r=>dot(r,v)>scale).length===k&&!roots.some(r=>G.map(q=>dot(q,r)).every((t,i)=>t*scale===v[i]))).map(v=>v.map(x=>S*x));
 else{hull=H.map(h=>h.map(x=>x*S));for(const v of L0){const pt=(h,t)=>h.map((x,j)=>x*t+v[j]*(S-t));let low=0n,high=S;while(low+1n<high){const m=(low+high)>>1n;if(H.every(h=>norm(pt(h,m))<=U*S*S))low=m;else high=m;}for(const h of H)hull.push(pt(h,low));if(norm(v)===U)hull.push(v.map(x=>x*S));}}
 if(!hull.length)continue;const t={k,C:C.map(r=>index.get(r.join())),h:hull.map(x=>x.map(Number))};types.push(t);f.v=t;
 }const next=new Map();for(const L of levels)for(const r of maximal(positive.filter((_,i)=>!L.includes(i)))){const b=L.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(b.join(),b);}levels=[...next.values()];
}

const K=width;const neg=roots.map(r=>index.get(r.map(x=>-x).join())),axis=roots.flatMap((_,i)=>i<neg[i]?[i]:[]),ar=new Uint8Array(126);axis.forEach((i,j)=>ar[i]=ar[neg[i]]=j);
const perms=I.map(j=>Uint8Array.from(roots,r=>index.get(reflect(r,j).join()))),ID=Uint8Array.from(roots,(_,i)=>i),B=Array.from({length:126},(_,i)=>1n<<BigInt(i)),ms=ids=>ids.reduce((m,i)=>m|B[i],0n),pop=m=>{let s=0;for(;m;m&=m-1n)s++;return s;};
const rr=roots.map(r=>r.map(Number)),g=G.map(r=>r.map(Number)),ad=adj.map(r=>r.map(Number)),dd=(a,b)=>a.reduce((s,v,i)=>s+v*b[i],0),gr=(r,s)=>dd(r,g.map(t=>dd(t,s)));
const compose=(p,q)=>Uint8Array.from(q,i=>p[i]),inv=p=>{const z=new Uint8Array(p.length);for(let i=0;i<p.length;i++)z[p[i]]=i;return z;},ft=new Map(formal.map(t=>[ms(t.C),t]));
function rec(v){const s=I.map(i=>v.reduce((a,j)=>a+rr[j][i],0));let p=ID;for(let it=0;;it++){if(it>63)throw Error('dominant loop');const i=I.find(j=>dd(s,g[j])<0);if(i===undefined)break;s[i]-=dd(s,g[i]);p=compose(perms[i],p);}const t=ft.get(ms(v.map(i=>p[i])));if(!t)return null;const h=inv(p);if(ms(t.C.map(i=>h[i]))!==ms(v))throw Error('transport');return {t,h};}
for(const t of formal.filter(t=>t.k>=6&&t.k<K)){for(let i=0;i<126;i++){if(t.C.includes(i)||t.C.includes(neg[i]))continue;const z=rec(t.C.concat(i));if(z)t.ch.push({i,...z});}}
const seeds=[];for(const t of formal.filter(t=>t.k===6)){const S=[{t,p:ID,rs:t.C,m:ms(t.C),u:ms(t.C.map(i=>ar[i]))}],seen=new Set([S[0].m]);
 for(let i=0;i<S.length;i++)for(const q of perms){const r=S[i].rs.map(j=>q[j]),m=ms(r);if(seen.has(m))continue;seen.add(m);S.push({t,p:compose(q,S[i].p),rs:r,m,u:ms(r.map(j=>ar[j]))});}seeds.push(...S);}
const secs=axis.map(r=>ms(axis.flatMap((y,i)=>gr(rr[r],rr[y])===0?[i]:[]))),axes=axis.map((_,i)=>i);let cpool=0;
function near(A,e){const seen=new Map(),buckets=new Map();
 for(const v of seeds){let ext=v.u&~A;if(pop(ext)<=e)seen.set(v.m,{...v,ext});}
 for(const v of seen.values()){if(v.t.v){let p=buckets.get(v.ext);if(!p){p=[];buckets.set(v.ext,p);}p.push(v);}
  for(const {i,t,h}of v.t.ch){const b=v.p[i],m=v.m|B[b];if(seen.has(m))continue;const u=v.u|B[ar[b]],ext=u&~A;if(pop(ext)>e)continue;seen.set(m,{t,p:compose(v.p,h),rs:v.rs.concat(b),m,u,ext});}
 }cpool+=seen.size;return buckets;
}
function allMatch(V){if(V.length<=6)return true;const m=new Int32Array(126).fill(-1);for(let i=0;i<V.length;i++){const used=new Uint8Array(126);function aug(j){for(const k of V[j].rs){if(used[k])continue;used[k]=1;if(m[k]<0||aug(m[k])){m[k]=j;return true;}}return false;}if(!aug(i))return false;}return true;}
for(const f of formal.filter(t=>t.v)){
 const t=f.v,sum=I.map(i=>f.C.reduce((a,j)=>a+rr[j][i],0)),J=I.filter(i=>dd(sum,g[i])===0),S=[...new Map(t.h.map(h=>[h.join(),h])).values()],seen=new Set(S.map(h=>h.join()));
 for(let i=0;i<S.length;i++)for(const j of J){const h=S[i].map((x,k)=>x-g[k][j]*S[i][j]),s=h.join();if(!seen.has(s)){seen.add(s);S.push(h);}}
 t.s=S.map(h=>{const a=h.map(BigInt),n=norm(a),c=new Set(f.C),yes=roots.every((r,i)=>{const z=dot(r,a);return (z>0n&&2n*determinant*z*z>n)===c.has(i);});return {h,n,yes};});
}
function hull(v){if(v.h)return v.h;const p=inv(v.p),M=I.map(i=>rr[p[i]]);v.h=v.t.v.s.map(({h,n,yes})=>{const H=h.map(BigInt),a=M.map(r=>dot(r.map(BigInt),H)),w=adj.map(r=>dot(r,a));return {v:a,d:w,n,yes};});return v.h;}
function incompatible(a,b){if(!a.c)a.c=new Map();if(a.c.has(b.m))return a.c.get(b.m);const A=hull(a),H=hull(b);let lin=true,ang=true;const threshold=determinant*(scale*S)**2n;
 outer:for(const x of A)for(const y of H){const z=dot(x.d,y.v);if(z<=threshold)lin=false;const d=4n*z*z-x.n*y.n;if(z<=0n||d<0n||d===0n&&x.yes&&y.yes)ang=false;if(!lin&&!ang)break outer;}
 const ok=lin||ang;
 a.c.set(b.m,ok);if(!b.c)b.c=new Map();b.c.set(a.m,ok);return ok;
}
function rainbow(V){const colors=Array.from({length:126},()=>[]);let nodes=0;function go(P){if(!P.length){const found=new Set();for(let r=0;r<126;r++)for(const i of colors[r]){if(found.has(i)||!V[i].rs.includes(r)||colors[r].some(j=>j!==i&&!incompatible(V[i],V[j])))throw Error("bad displayed color class");found.add(i);}if(found.size!==V.length)throw Error("incomplete coloring");return true;}if(++nodes>1600)return false;let b=-1,opt=null;for(const i of P){const vs=V[i].rs.filter(r=>colors[r].every(j=>incompatible(V[i],V[j])));if(!vs.length)return false;if(!opt||vs.length<opt.length){b=i;opt=vs;}}
 opt.sort((a,b)=>colors[a].length-colors[b].length);for(const r of opt){colors[r].push(b);if(go(P.filter(i=>i!==b)))return true;colors[r].pop();}return false;}return go(V.map((_,i)=>i));}


if(job==='core'){
function stabilizer(t){const sum=I.map(i=>t.C.reduce((a,j)=>a+rr[j][i],0)),J=I.filter(i=>dd(sum,g[i])===0).map(i=>axis.map(a=>ar[perms[i][a]]));
 let S=[Uint8Array.from(axes)],vis=new Set(S.map(q=>String.fromCharCode(...q)));for(let i=0;i<S.length;i++)for(const a of J){const v=Uint8Array.from(S[i],j=>a[j]),c=String.fromCharCode(...v);if(!vis.has(c)){vis.add(c);S.push(v);}}return S;}
function orbitSub(F,H,n,x,visit){if(!n){visit(x);return;}if(F.length<n)return;
 if(H.length===1){function choose(i,left,u){if(!left){visit(u);return;}for(let j=i;j<=F.length-left;j++)choose(j+1,left-1,u|B[F[j]]);}choose(0,n,x);return;}
 let used=new Set();for(const r of F){if(used.has(r))continue;const S=[...new Set(H.map(p=>p[r]))];let suffix=F.filter(i=>!used.has(i)&&i!==r);
  if(suffix.length>=n-1)orbitSub(suffix,H.filter(p=>p[r]===r),n-1,x|B[r],visit);for(const q of S)used.add(q);}
}
let total=0,equator=0,mat=0,colors=0,hard=0,max=0;const examples=[],seenU=new Set();
for(const t of types){const A=ms(t.C.map(i=>ar[i])),e=K-t.k,bag=near(A,e),F=axes.filter(i=>!(A&B[i])),L=secs.map(s=>[s,pop(s&A)]).filter(z=>z[1]<2);
 function ext(x){const U=A|x;if(seenU.has(U))return;seenU.add(U);total++;
 if(L.some(([s,a])=>{let t=s&x;return !t||(!a&&!(t&(t-1n)));})){equator++;return;}
 const vs=[];for(let z=x;;z=(z-1n)&x){const p=bag.get(z);if(p)vs.push(...p);if(!z)break;}max=Math.max(max,vs.length);if(allMatch(vs)){mat++;return;}if(rainbow(vs)){colors++;return;}hard++;if(examples.length<6)examples.push([U.toString(),vs.length]);
 }orbitSub(F,stabilizer(t),e,0n,ext);console.log('anchor',K,t.k,total,equator,mat,colors,hard,max);
}console.log('E7 core',K,total,equator,mat,colors,hard,max,cpool);if(total!==1521201||hard!==0||equator!==406849||mat!==984451||colors!==129901)throw Error('core census');
}else{
const threshold=determinant*(scale*S)**2n;
function possiblyNeg(a,b){const X=hull(a),Y=hull(b);for(const x of X)for(const y of Y)if(dot(x.d,y.v)<-threshold)return true;return false;}

const TT=formal.filter(t=>t.v&&t.k<=K-6),zero=v=>I.map(i=>v.reduce((a,j)=>a+rr[j][i],0));
const refl=axis.map(j=>{const r=rr[j];return Uint8Array.from(rr,s=>{const g=gr(s,r);const z=s.map((x,i)=>x-g*r[i]);return index.get(z.join());});});
const pairs=[];for(const t of TT.filter(t=>2*t.k<=K)){const a={t,p:ID,rs:t.C,m:ms(t.C),u:ms(t.C.map(i=>ar[i]))},s0=zero(t.C),J=I.filter(i=>dd(s0,g[i])===0);
 for(const j of J)if(ms(a.rs.map(i=>perms[j][i]))!==a.m)throw Error('anchor stabilizer');
 let ct=0,nneg=0;for(const v of TT.filter(v=>v.k>=t.k&&v.k+t.k<=K)){
 function fold(rs,P){
  const s=zero(rs),qs=[];
  for(;;){const i=J.find(j=>dd(s,g[j])<0);if(i===undefined)break;s[i]-=dd(s,g[i]);rs=rs.map(j=>perms[i][j]);qs.push(perms[i]);}
  return {rs,qs,m:ms(rs)};
 }
 const one=fold(v.C),seen=new Set([one.m]),L=[{t:v,p:one.qs.reduce((p,q)=>compose(q,p),ID),rs:one.rs,m:one.m,u:ms(one.rs.map(i=>ar[i]))}];
 for(let i=0;i<L.length;i++){const f=L[i];
 if(!(f.m&a.m)&&pop(a.u&f.u)<=63){ct++;if(possiblyNeg(a,f)){pairs.push([a,f]);nneg++;}}
 for(const q of refl){const r=fold(f.rs.map(j=>q[j]));if(seen.has(r.m))continue;seen.add(r.m);const p=r.qs.reduce((p,x)=>compose(x,p),compose(q,f.p));if(ms(v.C.map(j=>p[j]))!==r.m)throw Error('pair transport');
 L.push({t:v,p,rs:r.rs,m:r.m,u:ms(r.rs.map(j=>ar[j]))});}
 } }console.log('candidates',t.k,ct,nneg);}
console.log('pairs',pairs.length);
const signed=secs.map(s=>ms(roots.flatMap((_,i)=>s&B[ar[i]]?[i]:[])));const stats={n:0,equator:0,count:0,degree:0,rainbow:0,clique:0,hard:0,peak:0};let unresolved=[];
for(const [a,b] of pairs){const A=a.u|b.u,M=a.m|b.m,e=K-a.t.k-b.t.k,bag0=near(A,e),bag=new Map();for(const vs of bag0.values())for(const v of vs){const ext=v.m&~M;if(pop(ext)>e)continue;if(!bag.has(ext))bag.set(ext,[]);bag.get(ext).push(v);}
 let sub=0;
 function term(x){const U=M|x;sub++;stats.n++;
 if(signed.some(s=>pop(s&U)<=2)){stats.equator++;return;}
 const V=[];for(let z=x;;z=(z-1n)&x){const l=bag.get(z);if(l)V.push(...l);if(!z)break;}
 stats.peak=Math.max(stats.peak,V.length);if(V.length<K+1){stats.count++;return;}
 const rd=new Uint8Array(126);for(const v of V)for(const i of v.rs)rd[i]++;if(roots.some((_,i)=>(U&B[i])&&rd[i]<2)){stats.degree++;return;}
 if(rainbow(V)){stats.rainbow++;return;}
 let nodes=0;function test(P,target){if(P.length<target)return false;if(target<=1)return true;if(++nodes>30000)return null;const deg=P.map(i=>P.reduce((s,j)=>s+Number(i!==j&&incompatible(V[i],V[j])),0)),largest=Math.max(...deg);if(largest===0)return true;const idx=deg.indexOf(largest),i=P[idx],Q=P.filter(j=>j!==i);const x=test(Q.filter(j=>!incompatible(V[i],V[j])),target-1);if(x!==false)return x;return test(Q,target);}
 const ok=test(V.map((v,i)=>i),K+1);if(ok===false){stats.clique++;return;}stats.hard++;if(unresolved.length<15)unresolved.push([a.rs,b.rs,x.toString(),V.length,nodes,ok]);}

 const byRoot=roots.map(()=>[]),adds=[...bag.keys()].filter(t=>t);for(const [ext,vs]of bag)for(const v of vs)for(const i of v.rs)byRoot[i].push(ext);
 const seen=new Set();let nodes=0;
 function ext(x){if(seen.has(x))return;seen.add(x);nodes++;const c=pop(x),U=M|x,left=e-c;if(!left){term(x);return;}
  if(signed.some(s=>pop(s&U)+left<=2))return;
  let opt=adds,min=1e8;
  for(let i=0;i<126;i++)if(U&B[i]){const extSet=new Set();let contained=0,may=0;
    for(const z of byRoot[i]){const y=x|z;if(y===x){if(++contained>=2)break;}else if(pop(y)<=e){extSet.add(y);may++;}}
    if(contained>=2)continue;if(contained+may<2)return;
    if(extSet.size<min){opt=[...extSet];min=extSet.size;}
  }
  for(const z of opt){const y=x|z;if(x!==y&&pop(y)<=e)ext(y);}
 }
 ext(0n);}
console.log('FINAL',K,JSON.stringify(stats),JSON.stringify(unresolved));if(stats.hard)throw Error('unresolved certificates');
}}
