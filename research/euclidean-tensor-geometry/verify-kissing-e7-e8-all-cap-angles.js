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
const n=Number(process.argv[2]||7);if(![7,8].includes(n))throw Error('rank');const I=Array.from({length:n},(_,i)=>i);
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
if(roots.length!==[126,240][n-7])throw Error("root count");
const positive=roots.filter(r=>r.every(v=>v>=0n));
const maximal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v>=r[i])));
const minimal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v<=r[i])));
const highest=maximal(positive)[0], H=G.map(row=>dot(row,highest));
const gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));
if(H.filter(x=>x>0n).length!==1)throw Error('dominant root ray');const nr=w=>w.some((x,i)=>x!==0n&&!H[i]);

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
 const candidates=eps=>Array.from({length:m},(_,i)=>i).filter(i=>cf[i]>eps);for(const eps of [1e-7,1e-4,0.005,0.02]){const possible=candidates(eps);if(possible.length<=n)exact(possible);if(cert)return cert;}
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
}if(tot!==[4160,25080][n-7])throw Error('ideal count');console.log('OUTPUT',n,JSON.stringify(out));

const walls=I.map(i=>positive.filter(r=>r[i]>0n).length),m=Math.min(...walls),ids=I.filter(i=>walls[i]===m),W=ids.map(i=>E[i]),raysSeen=new Set(W.map(v=>v.join()));for(let j=0;j<W.length;j++)for(const i of I){const v=W[j].map((u,k)=>u-W[j][i]*G[i][k]);if(!raysSeen.has(v.join())){raysSeen.add(v.join());W.push(v);}}console.log(n,'walls',walls,'H',H.join(),'nrM',Math.min(...walls.filter((_,i)=>nr(E[i]))),'signed',W.length);
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

const target=n===7?{M:27,nrM:27,rays:56,noA:[1,28,29,30,31,32,33],noB:[1,2,3,4,5]}:{M:57,nrM:78,rays:240,noA:[1,...Array.from({length:21},(_,i)=>i+37)],noB:[1,2,3,4,5,6,7]};
if(m!==target.M||Math.min(...walls.filter((_,i)=>nr(E[i])))!==target.nrM||W.length!==target.rays||ids.length!==1)throw Error('hemisphere witnesses');
if(out.filter(r=>r[0]&&!r[3]).map(r=>r[0]).join()!==target.noA.join()||out.filter(r=>!r[5]).map(r=>r[0]).join()!==target.noB.join())throw Error('equality flags');
discrepancy(n,roots.length,m,out.map(r=>[r[0],rational(r[2]),rational(r[4])]));
console.log('PASS',n,'discrepancy',(roots.length/2-m)+'/'+roots.length);
