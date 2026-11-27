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
const I=Array.from({length:6},(_,i)=>i);
const E=I.map(i=>I.map(j=>BigInt(i===j)));
const G=I.map(i=>I.map(j=>i===j?2n:
  (i<5&&j<5&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===5)?-1n:0n));
const determinant=det(G);
const adj=I.map(i=>I.map(j=>BigInt((i+j)%2?-1:1)*det(G.filter((_,k)=>k!==j).map(row=>row.filter((_,k)=>k!==i)))));
const roots=E.map(r=>r.slice()), index=new Map(roots.map((r,i)=>[r.join(),i]));
const reflect=(r,i)=>r.map((v,j)=>i===j?v-dot(G[i],r):v);
for(let j=0;j<roots.length;j++)for(const i of I){
  const r=reflect(roots[j],i);
  if(!index.has(r.join())){index.set(r.join(),roots.length);roots.push(r);}
}
if(roots.length!==72)throw Error("root count");
const positive=roots.filter(r=>r.every(v=>v>=0n));
const maximal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v>=r[i])));
const minimal=A=>A.filter(r=>!A.some(s=>s!==r&&s.every((v,i)=>v<=r[i])));
const highest=maximal(positive)[0], H=G.map(row=>dot(row,highest));
const gram=(a,b)=>dot(a,G.map(row=>dot(row,b)));
if(H.join()!=='0,0,0,0,0,1')throw Error('dominant root ray');
const reverse=w=>[w[4],w[3],w[2],w[1],w[0],w[5]];
const lab=C=>C.map(r=>r.join()).sort().join(';');

const norm=k=>dot(k,adj.map(row=>dot(row,k)));
function gcd(a,b){return b?gcd(b,a%b):a;}
function minimum(C){
 if(!C.length)return [0n,1n];const A=[...E,...minimal(C)], b=A.map((_,i)=>BigInt(i>=6)), Q=A.map(u=>A.map(v=>gram(u,v))),T=A.map(a=>G.map(row=>dot(row,a)));let cert=null;
 function visit(J,i){if(cert)return;if(J.length){
 const K=J.map(j=>J.map(k=>Q[j][k])),D=det(K);if(D>0n){const v=J.map(j=>b[j]),c=v.map((_,i)=>det(K.map((r,j)=>r.map((x,k)=>k===i?v[j]:x))));
 if(c.every(x=>x>=0n)){const w=I.map(i=>J.reduce((s,k,j)=>s+c[j]*T[k][i],0n));
 if(A.every((r,j)=>dot(r,w)>=D*b[j])){const p=dot(c,v),g=gcd(p,D);cert=[p/g,D/g,w.slice(0,5).some(z=>z!==0n)];return;}}}}
 if(J.length<6)for(let j=i;j<A.length;j++)visit(J.concat([j]),j+1);}
 visit([],0);if(!cert)throw Error('no KKT');return cert;
}
function largest(C){
 const U=maximal(positive.filter(r=>!C.includes(r)));
 if(I.some(i=>!U.some(r=>r[i])))return [1n,0n,true];
 const A=[...E,...U], b=A.map((_,i)=>BigInt(i>=6));let best=[0n,1n,false];
 function visit(J,i){if(J.length===6){const K=J.map(j=>A[j]), B=J.map(j=>b[j]);let D=det(K);if(!D)return;
 const V=I.map(i=>det(K.map((r,j)=>r.map((x,k)=>k===i?B[j]:x))));if(D<0n){D=-D;for(let i=0;i<6;i++)V[i]=-V[i];}
 if(V.some(x=>x<0n)||U.some(r=>dot(r,V)>D))return;const a=norm(V),dd=determinant*D*D,diff=a*best[1]-dd*best[0];if(diff>=0n){const g=gcd(a,dd);best=[a/g,dd/g,V.slice(0,5).some(x=>x!==0n)||(!diff&&best[2])];}return;}
 for(let j=i;j<=A.length-6+J.length;j++)visit(J.concat([j]),j+1);}
 visit([],0);return best;
}
const z=largest([]);let cur=[[]],tot=1,out=[[0,1,1,'0/1',0,z.slice(0,2).join('/'),+z[2]]];for(let k=1;k<=36;k++){const next=new Map();for(const S of cur)for(const r of maximal(positive.filter((_,i)=>!S.includes(i)))){const D=S.concat([positive.indexOf(r)]).sort((a,b)=>a-b);next.set(D.join(),D);}cur=[...next.values()];tot+=cur.length;const seen=new Set();let best=null,high=null;
 for(const S of cur){const C=S.map(i=>positive[i]),u=lab(C),v=lab(C.map(reverse)),ky=u<v?u:v;if(seen.has(ky))continue;seen.add(ky);const d=minimum(C);const c=best?d[0]*best[1]-best[0]*d[1]:-1n;if(c<0n){best=d;}else if(!c&&d[2])best[2]=true;const q=largest(C),g=high?q[0]*high[1]-high[0]*q[1]:1n;if(g>0n){high=q;}else if(!g&&q[2])high[2]=true;}
 out.push([k,cur.length,seen.size,best.slice(0,2).join('/'),+best[2],high.slice(0,2).join('/'),+high[2]]);}const expected=[[0,1,1,"0/1",0,"4/3",1],[1,1,1,"1/2",0,"2/1",0],[2,1,1,"2/3",1,"2/1",0],[3,1,1,"3/4",1,"2/1",0],[4,2,1,"4/5",1,"2/1",0],[5,3,2,"5/6",1,"10/3",1],[6,3,2,"1/1",1,"10/3",1],[7,4,3,"1/1",1,"10/3",1],[8,6,4,"1/1",1,"4/1",1],[9,7,4,"5/4",1,"4/1",1],[10,8,5,"5/4",1,"4/1",1],[11,10,6,"5/4",1,"6/1",1],[12,12,7,"4/3",1,"6/1",1],[13,14,8,"4/3",1,"22/3",1],[14,16,9,"4/3",1,"22/3",1],[15,19,11,"4/3",1,"8/1",1],[16,22,13,"4/3",1,"1/0",1],[17,25,14,"2/1",0,"1/0",1],[18,27,15,"2/1",0,"1/0",1],[19,31,17,"2/1",0,"1/0",1],[20,34,19,"2/1",0,"1/0",1],[21,38,21,"2/1",0,"1/0",1],[22,40,22,"10/3",1,"1/0",1],[23,44,24,"10/3",1,"1/0",1],[24,45,25,"10/3",1,"1/0",1],[25,49,27,"10/3",1,"1/0",1],[26,50,27,"16/3",1,"1/0",1],[27,51,28,"6/1",1,"1/0",1],[28,50,27,"6/1",1,"1/0",1],[29,50,28,"6/1",1,"1/0",1],[30,46,25,"10/1",1,"1/0",1],[31,41,23,"34/3",1,"1/0",1],[32,35,19,"46/3",1,"1/0",1],[33,25,15,"18/1",1,"1/0",1],[34,15,9,"30/1",1,"1/0",1],[35,6,4,"42/1",1,"1/0",1],[36,1,1,"78/1",1,"1/0",1]];if(tot!==833||JSON.stringify(out)!==JSON.stringify(expected))throw Error('angular spectrum');console.log(tot,JSON.stringify(out));
const wall=I.map(i=>positive.filter(r=>r[i]>0n).length);if(Math.min(...wall)!==16||H.some((x,i)=>x>0n&&wall[i]===16))throw Error('open hemisphere');

for(let k=21;k<=36;k++){const [p,q]=out[k][3].split('/').map(BigInt);if(4096n*q>2n*p*BigInt(56-k)**2n)throw Error('cap discrepancy inequality');}
if(String(wall)!=='16,25,29,25,16,21')console.log('hemisphere rays',wall);if(I.filter(i=>wall[i]===16).join()!=='0,4')throw Error('hemisphere minimizers');
const weights=[E[0],E[4]],wm=new Set(weights.map(v=>v.join()));for(const w of weights)for(const i of I){const y=I.map(j=>w[j]-w[i]*G[i][j]);if(!wm.has(y.join())){wm.add(y.join());weights.push(y);}}if(wm.size!==54)throw Error('oriented hemisphere count');console.log('hemisphere normals',wm.size);
