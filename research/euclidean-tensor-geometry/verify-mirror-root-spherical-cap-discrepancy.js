// Spherical-cap discrepancy: finite checks for the uniform irreducible classification.
'use strict';
const assert=require('node:assert/strict');
// Rational enclosures for integrals of the unit-sphere coordinate density.
// Every grid bound is directed outwards. No floating-point decision is used.
const U=2048n,cache=new Map();
function grid(d){
 if(cache.has(d))return cache.get(d);
 const h=BigInt(d-3),den=(U*U)**h,q=U*U,lo=[0n],hi=[0n],low=[],high=[];
 for(let i=0n;i<=U;i++){const a=q*(q-i*i)**h,b=a/den;
  let l=0n,r=U+1n;while(r-l>1n){const m=(r+l)/2n;if(m*m<=b)l=m;else r=m;}
  low.push(l);high.push(l*l*den===a?l:l+1n);
 }
 for(let i=1;i<=Number(U);i++){lo[i]=lo[i-1]+low[i];hi[i]=hi[i-1]+high[i-1];}
 let p=d%2?1n:1n,b=d%2?2n:1n;for(let i=d%2?3:2;i<d;i+=2){p*=BigInt(i);b*=BigInt(i-1);}
 // 333/106 < pi < 355/113; even-dimensional normalization contains 1/pi.
 const g={lo,hi,lp:p*(d%2?1n:113n),lq:b*q*(d%2?1n:355n),hp:p*(d%2?1n:106n),hq:b*q*(d%2?1n:333n)};cache.set(d,g);return g;
}
// A=[a,b,q] means (a+b*lambda)/q, lambda^2=H*lambda+J,
// H,J=(0,2) or (1,1); returns bounds for 1/2-F(1/sqrt(2A)).
function dec(d,A,H=0n,J=2n){const [a,b,q]=A.map(BigInt);
 if(q<=0n)throw Error('not finite');const sg=x=>x>0n?1:x<0n?-1:0;
 const sign=(x,y)=>{const u=2n*x+H*y;if(!u)return sg(y);if(!y||sg(u)===sg(y))return sg(u);return sg(u)*sg(u*u-(H*H+4n*J)*y*y);};
 const gap=x=>sign(2n*a*x*x-q*U*U,2n*b*x*x);
 if(gap(U)<0)throw Error('cut > 1');let l=0n,r=U+1n;
 while(r-l>1n){const m=(r+l)/2n;if(gap(m)<=0)l=m;else r=m;}
 const u=l+(gap(l)===0?0n:1n),g=grid(d);
 return [[g.lp*g.lo[Number(l)],g.lq],[g.hp*g.hi[Number(u)],g.hq]];
}
const rational=s=>{const [a,q]=s.split('/');return [a,0,q];};
function discrepancy(d,N,M,T,H=0n,J=2n){
 for(const [k,A,B] of T){if(2*k>N-2*M){const [, [p,q]]=dec(d,A,H,J);if(p*BigInt(N)>=q*BigInt(N-k-M))throw Error('excess '+k);}
  if(k<M){const [[p,q]]=dec(d,B,H,J);if(p*BigInt(N)<=q*BigInt(M-k))throw Error('deficit '+k);}
 }
}

for(let d=3;d<=15;d++){
 const [[a,b],[x,y]]=dec(d,[d,0,2]);assert(2n*BigInt(d)*a>b);assert(2n*BigInt(d)*x<y*BigInt(d-1));
 for(const l of [d+1,d]){if(d<(l===d?8:7))continue;
  const [, [v,w]]=dec(d,[d*(l-2),0,2*l]);assert(2n*BigInt(l)*v<w*BigInt(l-2));}
}
console.log('PASS finite dimension bounds');
function simplyLaced(kind,n){
// Exact lower and upper chamber norm envelopes, using integer determinants.
'use strict';



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
const I=Array.from({length:n},(_,i)=>i);
const E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:
  (kind==="A"?Math.abs(i-j)===1:((i<n-1&&j<n-1&&Math.abs(i-j)===1)||(Math.min(i,j)===n-3&&Math.max(i,j)===n-1)))?-1n:0n));
const determinant=det(G);
const adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const roots=E.map(r=>r.slice()), index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){
  const r=reflect(roots[j],i);
  if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r);}
}
if(roots.length!==(kind==="A"?n*(n+1):2*n*(n-1)))throw Error("root count");
const positive=roots.filter(r=>r.every(v=>v>=0n));
const maximal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v>=r[i])));
const minimal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v<=r[i])));
const highest=maximal(positive)[0], H=G.map(row=>dot(row,highest));
const gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));
const nr=w=>w.some((x,i)=>x!==0n&&!H[i]);

const norm=k=>dot(k,adj.map(row=>dot(row,k)));
function gcd(a,b){return b?gcd(b,a%b):a;}
function minimum(C){
 if(!C.length)return [0n,1n];const A=[...E,...minimal(C)], b=A.map((_,i)=>BigInt(i>=n)), Q=A.map(u=>A.map(v=>gram(u,v))),T=A.map(a=>G.map(row=>dot(row,a)));let cert=null;
 function exact(J){if(J.length){
 const K=J.map(j=>J.map(k=>Q[j][k])),D=det(K);if(D>0n){const v=J.map(j=>b[j]),c=v.map((_,i)=>det(K.map((r,j)=>r.map((x,k)=>k===i?v[j]:x))));
 if(c.every(x=>x>=0n)){const w=I.map(i=>J.reduce((s,k,j)=>s+c[j]*T[k][i],0n));
 if(A.every((r,j)=>dot(r,w)>=D*b[j])){const p=dot(c,v),g=gcd(p,D);cert=[p/g,D/g,nr(w)];return;}}}}
 }
 const m=A.length,qf=Q.map(row=>row.map(Number)),cf=new Float64Array(m),sums=new Float64Array(m),bn=b.map(Number);for(let round=0;round<220;round++){let err=0;for(let i=0;i<m;i++){const delta=Math.max(0,cf[i]+(bn[i]-sums[i])/qf[i][i])-cf[i];if(!delta)continue;cf[i]+=delta;for(let j=0;j<m;j++)sums[j]+=delta*qf[i][j];err=Math.max(err,Math.abs(delta));}if(err<1e-10)break;}
 const candidates=I=>Array.from({length:m},(_,i)=>i).filter(i=>cf[i]>I);for(const eps of [1e-7,1e-4,0.005,0.02]){const possible=candidates(eps);if(possible.length<=n)exact(possible);if(cert)return cert;}
 function visit(J,i){if(cert)return;exact(J);if(cert)return;if(J.length<n)for(let j=i;j<A.length;j++)visit(J.concat([j]),j+1);}
 visit([],0);if(!cert)throw Error('no KKT');return cert;
}
function largest(C){
 const U=maximal(positive.filter(r=>!C.includes(r)));
 if(I.some(i=>!U.some(r=>r[i])))return [1n,0n,true];
 const A=[...E,...U], b=A.map((_,i)=>BigInt(i>=n));let best=[0n,1n,false];
 function visit(J,i){if(J.length===n){const K=J.map(j=>A[j]), B=J.map(j=>b[j]);let D=det(K);if(!D)return;
 const V=I.map(i=>det(K.map((r,j)=>r.map((x,k)=>k===i?B[j]:x))));if(D<0n){D=-D;for(let i=0;i<n;i++)V[i]=-V[i];}
 if(V.some(x=>x<0n)||U.some(r=>dot(r,V)>D))return;const a=norm(V),dd=determinant*D*D,diff=a*best[1]-dd*best[0];if(diff>=0n){const g=gcd(a,dd);best=[a/g,dd/g,nr(V)||(!diff&&best[2])];}return;}
 for(let j=i;j<=A.length-n+J.length;j++)visit(J.concat([j]),j+1);}
 visit([],0);return best;
}

const bits=positive.map((_,i)=>1n<<BigInt(i)),idx=new Map(positive.map((r,i)=>[r.join(),i]));
const above=positive.map(r=>I.reduce((m,j)=>{const v=r.slice();v[j]++;const k=idx.get(v.join());return k===undefined?m:m|bits[k];},0n));
const z=largest([]);let sets=[0n],tot=1,unbounded=false,out=[[0,1,'0/1',0,z.slice(0,2).join('/'),+z[2]]];
for(let k=1;k<=positive.length;k++){const next=new Set();for(const S of sets)for(let i=0;i<bits.length;i++)if(!(S&bits[i])&&((above[i]&S)===above[i]))next.add(S|bits[i]);sets=[...next];tot+=sets.length;let best=null,high=unbounded?[1n,0n,true]:null;
 for(const S of sets){const C=positive.filter((r,i)=>S&bits[i]);const d=minimum(C),c=best?d[0]*best[1]-best[0]*d[1]:-1n;if(c<0n)best=d;else if(!c&&d[2])best[2]=true;
 if(!unbounded){const q=largest(C),g=high?q[0]*high[1]-high[0]*q[1]:1n;if(g>0n)high=q;else if(!g&&q[2])high[2]=true;if(!high[1])unbounded=true;}}
 out.push([k,sets.length,best.slice(0,2).join('/'),+best[2],high.slice(0,2).join('/'),+high[2]]);
 if(k%10===0)console.log('tick',n,k,sets.length);
}const M=kind==='A'?n:2*(n-1),N=roots.length;
 if(out.find(r=>r[4]==='1/0')[0]!==M)throw Error('equator');
 discrepancy(n,N,M,out.map(v=>[v[0],rational(v[2]),rational(v[4])]));
 console.log('PASS',kind+n,'ideals',tot,'hemisphere',M,'/',N);

}
for(let d=3;d<=6;d++)simplyLaced('A',d);
for(let d=4;d<=7;d++)simplyLaced('D',d);
'use strict';

for(const [name,labels] of [['B3',[4,3]],['F4',[3,4,3]],['H3',[5,3]],['H4',[5,3,3]]]){
 const n=labels.length+1,I=Array.from({length:n},(_,i)=>i),H=BigInt(name[0]==='H'),J=H?1n:2n,disc=H?5n:8n;
 const Z=[0n,0n],O=[1n,0n],L=[0n,1n],an=(x,y)=>[x[0]+y[0],x[1]+y[1]],ne=x=>[-x[0],-x[1]],su=(x,y)=>an(x,ne(y)),mu=(x,y)=>[x[0]*y[0]+J*x[1]*y[1],x[0]*y[1]+x[1]*y[0]+H*x[1]*y[1]],sc=(x,i)=>[BigInt(i)*x[0],BigInt(i)*x[1]],di=(a,b)=>a.reduce((s,x,i)=>an(s,mu(x,b[i])),Z),sg=x=>x>0n?1:x<0n?-1:0;
 function sign(x){const a=2n*x[0]+H*x[1],b=x[1];if(!a)return sg(b);if(!b||sg(a)===sg(b))return sg(a);return sg(a)*sg(a*a-disc*b*b);}
 const det=M=>M.length?M[0].reduce((s,x,i)=>!sign(x)?s:an(s,sc(mu(x,det(M.slice(1).map(r=>r.filter((_,j)=>j!==i)))),i%2?-1:1)),Z):O;
 function solve(M,b){let d=det(M);if(!sign(d))return null;let w=M.map((_,i)=>det(M.map((r,j)=>r.map((v,k)=>k===i?b[j]:v))));if(sign(d)<0){d=ne(d);w=w.map(ne);}return [w,d];}
 function combos(m,q,fn,ix=[],j=0){if(ix.length===q)return !!fn(ix);for(let k=j;k<=m-q+ix.length;k++)if(combos(m,q,fn,ix.concat([k]),k+1))return true;return false;}
 const E=I.map(i=>I.map(j=>i===j?O:Z)),G=I.map(i=>I.map(j=>i===j?sc(O,2):Math.abs(i-j)!==1?Z:ne(labels[Math.min(i,j)]===3?O:L))),D=det(G),adj=I.map(i=>I.map(j=>sc(det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i))),(i+j)%2?-1:1))),R=E.slice(),seen=new Set(R.map(r=>r.join(';')));
 for(let t=0;t<R.length;t++)for(const i of I){const r=R[t].slice();r[i]=su(r[i],di(G[i],r));const k=r.join(';');if(!seen.has(k)){seen.add(k);R.push(r);}}
 const pos=R.filter(r=>r.every(t=>sign(t)>=0)),N=R.length,ids=pos.map((_,i)=>i),bits=ids.map(i=>1n<<BigInt(i)),dom=(a,b)=>a.every((v,i)=>sign(su(v,b[i]))>=0),up=ids.map(i=>ids.reduce((m,j)=>i!==j&&dom(pos[j],pos[i])?m|bits[j]:m,0n)),down=ids.map(i=>ids.reduce((m,j)=>i!==j&&dom(pos[i],pos[j])?m|bits[j]:m,0n));
 const gram=(a,b)=>di(a,G.map(row=>di(row,b))),sq=w=>di(w,adj.map(row=>di(row,w))),cmp=(f,g)=>sign(su(mu(f[0],g[1]),mu(f[1],g[0])));
 function min(m){if(!m)return [Z,O];const xs=ids.filter(i=>(m&bits[i])&&!(m&down[i])),A=E.concat(xs.map(i=>pos[i])),b=A.map((_,i)=>i>=n?O:Z),K=A.map(r=>A.map(s=>gram(r,s))),ga=A.map(r=>G.map(row=>di(row,r)));let ret=null;
 for(let t=1;t<=n&&!ret;t++)combos(A.length,t,ix=>{const out=solve(ix.map(i=>ix.map(j=>K[i][j])),ix.map(i=>b[i]));if(!out||out[0].some(v=>sign(v)<0))return false;const [p,d]=out,w=I.map(i=>ix.reduce((s,j,l)=>an(s,mu(p[l],ga[j][i])),Z));if(A.some((r,i)=>sign(su(di(r,w),mu(d,b[i])))<0))return false;ret=[di(p,ix.map(i=>b[i])),d];return true;});assert(ret);return ret;}
 function max(m){const xs=ids.filter(i=>!(m&bits[i])&&!(up[i]&~m));if(I.some(j=>xs.every(i=>!sign(pos[i][j]))))return [O,Z];const A=E.concat(xs.map(i=>pos[i])),b=A.map((_,i)=>i>=n?O:Z);let ret=[Z,O];
 combos(A.length,n,ix=>{const t=solve(ix.map(i=>A[i]),ix.map(i=>b[i]));if(!t)return false;const [v,d]=t;if(v.some(x=>sign(x)<0)||xs.some(i=>sign(su(di(pos[i],v),d))>0))return false;const a=[sq(v),mu(D,mu(d,d))];if(cmp(a,ret)>0)ret=a;return false;});return ret;}
 const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;function norm(f){if(!sign(f[1]))return [1,0,0];const co=[f[1][0]+H*f[1][1],-f[1][1]],z=mu(f[1],co)[0],p=mu(f[0],co),g=BigInt(sg(z))*gcd(gcd(z,p[0]),p[1]);return [String(p[0]/g),String(p[1]/g),String(z/g)];}
 let lvl=new Set([0n]),unb=false,out=[],tot=0;for(let k=0;k<=pos.length;k++){let low=null,hi=unb?[O,Z]:null;for(const m of lvl){const a=min(m);if(!low||cmp(a,low)<0)low=a;if(!unb){const b=max(m);if(!hi||cmp(b,hi)>0)hi=b;if(!sign(hi[1]))unb=true;}}
 tot+=lvl.size;out.push([k,norm(low),norm(hi)]);let next=new Set();for(const m of lvl)for(const i of ids)if(!(bits[i]&m)&&!(up[i]&~m))next.add(m|bits[i]);lvl=next;}
 const walls=I.map(i=>pos.filter(r=>sign(r[i])).length),M=Math.min(...walls),V=I.filter(i=>walls[i]===M).map(i=>E[i]),seenW=new Set(V.map(x=>x.join(';')));
 for(let j=0;j<V.length;j++)for(const i of I){const w=V[j].map((v,k)=>su(v,mu(V[j][i],G[i][k]))),z=w.join(';');if(!seenW.has(z)){seenW.add(z);V.push(w);}}
 const expected={B3:[18,5,6],F4:[48,15,48],H3:[30,10,12],H4:[120,45,120]}[name];assert.deepEqual([N,M,V.length],expected);
 discrepancy(n,N,M,out,H,J);console.log('PASS',name,'ideals',tot,'walls',walls.join(','),'signed minimizers',V.length);
}
