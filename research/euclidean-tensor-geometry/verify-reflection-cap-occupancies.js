'use strict';
const maximum=n=>Math.max(2*n-2,Math.min(n,7)*(Math.min(n,7)-1)/2);
const lim=n=>Math.max(2*n-1,[0,0,3,6,9,12,16,21,21,21,21,21,21][n]||0);
let bad=[];for(let n=2;n<=12;n++){let count=0,exc=0;for(let m=0;m<1<<(n-1);m++){
const v=Array.from({length:n},(_,i)=>i),E=[],adj=v.map(()=>[]);for(let j=1;j<n;j++)if(m>>(j-1)&1)for(let i=0;i<j;i++){adj[i].push(j);adj[j].push(i);E.push([i,j]);}
const sort=v.slice().sort((a,b)=>adj[b].length-adj[a].length);
for(let h=0;h<=Math.min(n,3);h++){if(E.length+h<=lim(n))continue;exc++;const H=new Set(sort.slice(0,h));
function matching(V,b){if(!b)return true;if(!V.length)return false;const i=V[0];if(H.has(i)&&matching(V.slice(1),b-1))return true;for(const j of adj[i])if(V.includes(j)&&matching(V.filter(k=>k!==i&&k!==j),b-1))return true;return matching(V.slice(1),b);}
if(matching(v,4))continue;let bic=false;for(const i of v)for(const j of v)if(j<i)for(const k of v)if(k<j&&adj[i].filter(x=>adj[j].includes(x)&&adj[k].includes(x)).length>=6)bic=true;if(bic)continue;
const rows=E.map(ij=>ij).concat([...H].map(i=>[i])),w=rows.map(()=>0),a=v.map(()=>0);for(let step=0;step<300;step++)for(const [k,row] of rows.entries()){const rhs=row.length===1?Math.SQRT1_2:1,d=Math.max(-w[k],(rhs-row.reduce((z,i)=>z+a[i],0))/row.length);w[k]+=d;row.forEach(i=>a[i]+=d);}
const norm=a.reduce((s,x)=>s+x*x,0);const W=w.map(x=>BigInt(Math.round(x*1000000))),u=v.map(()=>0n);let p=0n,t=0n;for(const [j,row] of rows.entries()){if(row.length===1)t+=W[j];else p+=W[j];for(const k of row)u[k]+=W[j];}const U=u.reduce((z,a)=>z+a*a,0n),S=4n*U-2n*p*p-t*t;if(W.some(x=>x<0n)||!(p||t)||S>0n&&S*S>8n*p*p*t*t)bad.push([n,m,h,E.length,norm]);count++;}
}console.log({n,lim:lim(n),exc,count});}if(bad.length)throw Error('uncertified B bound');

function problem(n,type){const E=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>+(i===j))),dd=(u,v)=>u.reduce((s,t,i)=>s+t*v[i],0),rows=[],cone=E.map((v,i)=>v.map((x,j)=>x-(i+1===j?1:0))),columns=E.map((v,i)=>v.map((_,j)=>+(j<=i)));
if(type==='F'){cone[0]=[1,-1,-1,-1];columns.splice(0,4,[1,0,0,0],[1,1,0,0],[2,1,1,0],[3,1,1,1]);}
for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)for(const s of [-1,1])rows.push({r:E[i].map((v,k)=>2*(v+s*E[j][k])),t:4});for(const v of E)rows.push({r:v.map(k=>2*k),t:2});if(type==='F')for(let m=0;m<8;m++)rows.push({r:[1,...[0,1,2].map(k=>m>>k&1?-1:1)],t:2});for(const r of rows)r.b=columns.map(c=>dd(c,r.r));return {n,E,rows,cone,columns,dd};}
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

const add=(u,v)=>[u[0]+v[0],u[1]+v[1]],scale=(u,c)=>[u[0]*c,u[1]*c],mul=(u,v)=>[u[0]*v[0]+2n*u[1]*v[1],u[0]*v[1]+u[1]*v[0]],minus=(u,v)=>add(u,scale(v,-1n)),zero=[0n,0n];
function sign([a,b]){const s=x=>x>0n?1:x<0n?-1:0;if(!a)return s(b);if(!b||s(a)===s(b))return s(a);return s(a)*s(a*a-2n*b*b);}
function combine(A,k,fn,J=[],i=0){if(J.length===k){return !!fn(J);}for(let j=i;j<=A.length-k+J.length;j++)if(combine(A,k,fn,J.concat([j]),j+1))return true;return false;}
function lin(A,b){let D=det(A);if(!D)return null;const p=A.map((_,i)=>[0,1].map(k=>det(A.map((r,j)=>r.map((v,l)=>i===l?b[j][k]:v)))));if(D<0n){D=-D;return {D,p:p.map(u=>scale(u,-1n))};}return {D,p};}
function geometry(n,type,lower,upper,witnessLo,witnessHi){const {rows,cone,dd}=problem(n,type),idx=rows.map((_,i)=>i),bit=idx.map(i=>1n<<BigInt(i));
 const dom=(a,b)=>a.b.every((x,i)=>x*x*b.t>=b.b[i]*b.b[i]*a.t),up=idx.map(i=>idx.reduce((m,j)=>m|(j!==i&&dom(rows[j],rows[i])?bit[j]:0n),0n)),down=idx.map(i=>idx.reduce((m,j)=>m|(j!==i&&dom(rows[i],rows[j])?bit[j]:0n),0n));
 if(idx.some(i=>up[i]&down[i]))throw Error('equal or unordered duplications');
 function lvl(k){let f=new Set([0n]);for(let h=0;h<k;h++){const g=new Set();for(const m of f)for(const i of idx)if(!(m&bit[i])&&(m&up[i])===up[i])g.add(m|bit[i]);f=g;}return [...f];}
 function witness(a){const q=dd(a,a);if(rows.some(({r})=>dd(a,r)**2===q*dd(r,r)))throw Error('root witness');return rows.filter(({r,t})=>dd(a,r)>0&&2*dd(a,r)**2>t*q).length;}
 if(witnessLo[0] instanceof Array){
const {a,D}=({a:witnessLo.map(v=>v.map(BigInt)),D:2n});const Q=a.reduce((s,x)=>add(s,mul(x,x)),zero);if(sign(minus(Q,[2n*D*D,0n]))!==0)throw Error('witness radius');
let k=0;for(const {r,t} of rows){const u=a.reduce((s,x,i)=>add(s,scale(x,BigInt(r[i]))),zero);if(sign(minus(mul(u,u),scale(Q,BigInt(dd(r,r)))))===0)throw Error('root witness');if(sign(u)>0&&sign(minus(mul(u,u),[BigInt(t)*D*D,0n]))>0)k++;}
if(k!==lower)throw Error('lower count '+k);
}else if(witness(witnessLo)!==lower)throw Error('witness');if(witnessHi&&witness(witnessHi)!==upper)throw Error('upper witness');
 const RHS=i=>rows[i].t===4?[2n,0n]:[0n,1n];let eq=0,vct=0;
 const low=lvl(lower-1);for(const m of low){const k=idx.filter(i=>!(m&bit[i])&&(up[i]&~m)===0n),cs=cone.map(r=>r.map(x=>BigInt(-x))),A=cs.concat(k.map(i=>rows[i].r.map(BigInt)),[[2n,...Array(n-1).fill(0n)]]),b=cs.map(()=>zero).concat(k.map(RHS),[[3n,0n]]);
 combine(A,n,J=>{const t=lin(J.map(i=>A[i]),J.map(i=>b[i]));if(!t)return;const {p,D}=t;if(A.some((r,i)=>sign(minus(p.reduce((s,x,j)=>add(s,scale(x,r[j])),zero),scale(b[i],D)))>0))return;
 vct++;const q=p.reduce((s,x)=>add(s,mul(x,x)),zero),cmp=sign(minus(q,[2n*D*D,0n]));if(cmp>0)throw Error('lower witness '+[type,n,String(m)]);if(cmp===0){if(!rows.some(({r})=>{const v=p.reduce((s,x,j)=>add(s,scale(x,BigInt(r[j]))),zero);return sign(minus(mul(v,v),scale(q,BigInt(dd(r,r)))))===0;}))throw Error('nonroot equality');eq++;}
 });}
 let hi=0;if(upper){for(const m of lvl(upper+1)){hi++;const ids=idx.filter(i=>m&bit[i]&&!(down[i]&m)),A=cone.map(r=>r.map(BigInt)).concat(ids.map(i=>rows[i].r.map(BigInt))),b=cone.map(()=>zero).concat(ids.map(RHS)),gram=A.map(r=>A.map(s=>r.reduce((z,x,i)=>z+x*s[i],0n)));
 let ok=false;for(let j=1;j<=n&&!ok;j++)ok=combine(A,j,J=>{const D=lin(J.map(i=>J.map(k=>gram[i][k])),J.map(i=>b[i]));if(!D||D.p.some(x=>sign(x)<0))return false;const q=J.reduce((s,i,k)=>add(s,mul(b[i],D.p[k])),zero);return sign(minus(q,[2n*D.D,0n]))>=0;});
 if(!ok)throw Error('upper does not certify '+[n,type,String(m)]);}}
 console.log({n,type,lower,upper,lowIdeals:low.length,highIdeals:hi,verticesWithMultiplicity:vct,rootEqualities:eq});}
const W=[[15,5],[17,9,4],[15,9,3,3],[7,7,5,0,0],[16,8,8,8,8,0],[7,7,3,0,0,0,0]];for(let n=2;n<=7;n++)geometry(n,'B',Math.min(n,4),0,n<5?W[n-2]:Array.from({length:n},(_,i)=>i===0?[2,0]:i<=2?[0,1]:[0,0]),null);geometry(4,'F',6,11,[[1,1],[1,0],[1,0],[-1,1]],[4,1,0,0]);

for(let n=2;n<=12;n++){const {rows,dd}=problem(n,'B'),v=({2:[5,4],3:[1,1,1],4:[3,3,3,2],5:[16,16,16,8,8],6:[13,10,10,10,10,10]})[n]||Array.from({length:n},(_,i)=>n<12?+(i<7):+(i===0)),q=dd(v,v);if(rows.filter(({r,t})=>dd(r,v)>0&&2*dd(r,v)**2>t*q).length!==lim(n))throw Error('B maximum witness');}

{

const Z=[0n,0n],O=[1n,0n],phi=[0n,1n],two=[2n,0n],add=(x,y)=>[x[0]+y[0],x[1]+y[1]],neg=x=>[-x[0],-x[1]],sub=(x,y)=>add(x,neg(y)),mul=(x,y)=>[x[0]*y[0]+x[1]*y[1],x[0]*y[1]+x[1]*y[0]+x[1]*y[1]],scl=(x,n)=>[x[0]*BigInt(n),x[1]*BigInt(n)],dot=(a,b)=>a.reduce((s,x,i)=>add(s,mul(x,b[i])),Z),sgn=x=>x>0n?1:x<0n?-1:0;
function sign(x){const a=2n*x[0]+x[1],b=x[1];if(!a)return sgn(b);if(!b||sgn(a)===sgn(b))return sgn(a);return sgn(a)*sgn(a*a-5n*b*b);}
const det=M=>M.length?M[0].reduce((s,x,i)=>!sign(x)?s:add(s,scl(mul(x,det(M.slice(1).map(r=>r.filter((_,j)=>j!==i)))),i%2?-1:1)),Z):O;
function sys(n){const I=Array.from({length:n},(_,i)=>i),unit=I.map(i=>I.map(j=>j===i?O:Z)),G=I.map(i=>I.map(j=>i===j?two:Math.abs(i-j)!==1?Z:Math.min(i,j)===0?neg(phi):neg(O))),D=det(G),adj=I.map(i=>I.map(j=>scl(det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i))),(i+j)%2?-1:1)));let roots=unit.slice(),seen=new Set(roots.map(r=>r.join(';')));for(let k=0;k<roots.length;k++)for(const i of I){const v=roots[k].slice();v[i]=sub(v[i],dot(G[i],v));const key=v.join(';');if(!seen.has(key)){seen.add(key);roots.push(v);}}
 const pos=roots.filter(r=>r.every(x=>sign(x)>=0));if(roots.length!==(n===3?30:120)||pos.length*2!==roots.length)throw Error('H roots');return {I,unit,G,D,adj,roots,pos};}

function comb(n,k,fn,J=[],j=0){if(J.length===k)return !!fn(J);for(let a=j;a<=n-k+J.length;a++)if(comb(n,k,fn,J.concat([a]),a+1))return true;return false;}
function lin(M,b){let d=det(M);if(!sign(d))return null;let p=M.map((_,i)=>det(M.map((r,j)=>r.map((x,k)=>i===k?b[j]:x))));if(sign(d)<0){p=p.map(neg);d=neg(d);}return {d,p};}
function prove(n,lo,hi,wlo,whi){const {I,unit,G,D,adj,roots,pos}=sys(n),ids=pos.map((_,i)=>i),bit=ids.map(i=>1n<<BigInt(i)),dom=(a,b)=>a.every((x,i)=>sign(sub(x,b[i]))>=0),up=ids.map(i=>ids.reduce((z,j)=>z|(i!==j&&dom(pos[j],pos[i])?bit[j]:0n),0n)),dn=ids.map(i=>ids.reduce((z,j)=>z|(i!==j&&dom(pos[i],pos[j])?bit[j]:0n),0n));
 function ideals(k){let f=new Set([0n]);for(let s=0;s<k;s++){const g=new Set();for(const m of f)for(const i of ids)if(!(m&bit[i])&&(m&up[i])===up[i])g.add(m|bit[i]);f=g;}return [...f];}
 const gram=(a,b)=>dot(a,G.map(r=>dot(r,b))),energy=w=>dot(w,adj.map(r=>dot(r,w)));
 function test(v){const w=v.map(x=>Array.isArray(x)?x.map(BigInt):[BigInt(x),0n]),Q=energy(w);let cnt=0,root=false;for(const r of pos){const z=dot(r,w),a=mul(D,mul(z,z));if(!sign(sub(a,scl(Q,2)))&&sign(z)>0)root=true;if(sign(z)>0&&sign(sub(scl(a,2),Q))>0)cnt++;}return [cnt,root];}
 const low=ideals(lo-1),high=ideals(hi+1);let badLo=[],badHi=0,equal=0;
 for(const m of low){const xs=ids.filter(i=>!(m&bit[i])&&!(up[i]&~m)),A=unit.map(r=>r.map(neg)).concat(xs.map(i=>pos[i]),unit),b=unit.map(()=>Z).concat(xs.map(()=>O),unit.map(()=>two));comb(A.length,n,J=>{const t=lin(J.map(i=>A[i]),J.map(i=>b[i]));if(!t)return;const {p,d}=t;if(A.some((r,i)=>sign(sub(dot(r,p),mul(d,b[i])))>0))return;
 const e=energy(p),q=mul(D,mul(d,d)),c=sign(sub(e,scl(q,2)));if(c>0||c===0&&!pos.some(r=>!sign(sub(dot(r,p),scl(d,2)))))badLo.push([String(m),String(p),String(d),c,test(p)]);if(c===0)equal++;});
 }
 for(const m of high){const xs=ids.filter(i=>m&bit[i]&&!(dn[i]&m)),A=unit.concat(xs.map(i=>pos[i])),b=unit.map(()=>Z).concat(xs.map(()=>O)),K=A.map(r=>A.map(s=>gram(r,s)));let ok=false;for(let k=1;k<=n&&!ok;k++)ok=comb(A.length,k,J=>{const t=lin(J.map(i=>J.map(j=>K[i][j])),J.map(i=>b[i]));return t&&t.p.every(x=>sign(x)>=0)&&sign(sub(dot(t.p,J.map(i=>b[i])),scl(t.d,2)))>=0;});if(!ok)badHi++;}
 if(test(wlo).join()!==[lo,false].join()||test(whi)[0]!==hi||badLo.length||badHi)throw Error('H certificate');console.log({n,lo,hi,lowerIdeals:low.length,upperIdeals:high.length,equal});}
prove(3,6,10,[3,2,1],[0,0,1]);prove(4,21,26,[0,1,0,2],[1,0,0,0]);

}