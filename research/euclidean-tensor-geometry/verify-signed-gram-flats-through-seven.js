'use strict';
// Signed Gram configurations: diagonal 2, off-diagonal in {-1,0,1}.
const K=7;
function burn(k){let sum=0,ord=0;const E=[];for(let i=0;i<k;i++)for(let j=0;j<i;j++)E.push([i,j]);function ix(i,j){if(i<j)[i,j]=[j,i];return i*(i-1)/2+j;}eachOrd([Array.from({length:k},(_,i)=>i)],p=>{let Q=E.map(([i,j])=>ix(p[i],p[j])),cycles=[];let seen=Array(E.length).fill(false);for(let i=0;i<E.length;i++)if(!seen[i]){let z=i,mask=0;do{seen[z]=true;mask^=(1<<E[z][0])^(1<<E[z][1]);z=Q[z];}while(z!==i);cycles.push(mask);}for(let s=0;s<(1<<(k-1));s++){let t=1;for(let m of cycles){let x=m&s,p=0;while(x){p^=1;x&=x-1;}if(!p)t*=3;}sum+=t;ord++;}});if(!Number.isSafeInteger(sum)||sum%ord)throw Error('Burnside integer');return sum/ord;}
const allmax=[null,null,[],[],[5],[10,5],[18,10,6],[32,18,10]],allcounts=[0,1,2,5,18,100,1242,43425];
function eachOrd(groups,cb){let seq=[];function gr(j){if(j===groups.length){cb(seq);return;}let g=groups[j];function perm(U){if(!U){gr(j+1);return;}for(let i=0;i<g.length;i++)if(U>>i&1){seq.push(g[i]);perm(U^(1<<i));seq.pop();}}perm((1<<g.length)-1);}gr(0);}
function canon(A){const k=A.length;let W=A.map(x=>x.slice()),V=Array.from({length:k},()=>[]);for(let h=1;h<=k;h++){for(let i=0;i<k;i++)V[i].push(W[i][i]);if(h===k)break;W=W.map(row=>A.map(col=>col.reduce((a,b,j)=>a+b*row[j],0)));}
 let cols=V.map(v=>v.join(',')),sort=[...new Set(cols)].sort(),cc=cols.map(c=>sort.indexOf(c));for(let z=0;z<k;z++){let w=A.map((row,i)=>[cc[i],...sort.map((_,c)=>row.reduce((s,x,j)=>s+(i!==j&&cc[j]===c&&x!==0),0))].join(','));let G=[...new Set(w)].sort();cols=w;if(G.length===sort.length){sort=G;break;}sort=G;cc=w.map(c=>sort.indexOf(c));}
 const groups=sort.map(c=>cols.flatMap((x,i)=>x===c?[i]:[]));let best=Infinity;
 eachOrd(groups,ord=>{let val=0,par=Array.from({length:k},(_,i)=>i),sig=Array(k).fill(1);function f(i){let v=i,s=1;while(par[v]!==v){s*=sig[v];v=par[v];}return [v,s];}
 for(let i=0;i<k;i++)for(let j=0;j<i;j++){let v=A[ord[i]][ord[j]];if(v){const [a,x]=f(i),[b,y]=f(j);if(a!==b){par[a]=b;sig[a]=-v*x*y;v=-1;}else v*=x*y;}
 val=val*3+(v+1);}best=Math.min(best,val);});return best;}
function decode(code,k){let A=Array.from({length:k},(_,i)=>Array.from({length:k},(_,j)=>i===j?2:0));for(let i=k-1;i>=0;i--)for(let j=i-1;j>=0;j--){A[i][j]=A[j][i]=code%3-1;code=Math.floor(code/3);}if(code)throw Error('decode');return A;}
function adjug(A){const k=A.length;let B=Array.from({length:k},(_,i)=>Array.from({length:k},(_,j)=>Number(i===j))),cs=[1],adj,sg=0;for(let i=1;i<=k;i++){if(i===k)adj=B;B=B.map(row=>A.map(col=>col.reduce((s,x,j)=>s+x*row[j],0)));let c=-B.reduce((z,row,j)=>z+row[j],0)/i;if(!Number.isSafeInteger(c)||Math.abs(c)>1e8)throw Error('char coeff');cs.push(c);for(let j=0;j<k;j++)B[j][j]+=c;}
 let D=cs[k]*(-1)**k;if(!D)return null;if(k%2===0)adj=adj.map(w=>w.map(x=>-x));if(A.some((r,i)=>adj.some((c,j)=>r.reduce((s,x,t)=>s+x*c[t],0)!==(i===j?D:0))))throw Error('adjugate');let prev=1;for(let i=1;i<=k;i++){const y=Math.sign(cs[i]*(-1)**i);if(y){if(y!==prev)sg++;prev=y;}}return [D,adj,sg];}
function signedVectors(k){const v=[];for(let a=0;a<3**k;a++){let d=a,row=[];for(let i=0;i<k;i++){row.push(d%3-1);d=Math.floor(d/3);}if(row.find(x=>x!==0)===1)v.push(row);}return v;}
const sv=Array.from({length:K+1},(_,i)=>signedVectors(i)),dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
function clique(N){let best=[],S=Array.from({length:N.length},(_,i)=>i);function go(P,R){if(!P.length){if(R.length>best.length)best=R.slice();return;}if(R.length+P.length<=best.length)return;let lines=[];for(const v of P){let C=lines.find(C=>C.every(w=>!N[v][w]));if(!C){C=[];lines.push(C);}C.push(v);}
 for(let k=lines.length-1;k>=0;k--){if(R.length+k+1<=best.length)return;let earlier=lines.slice(0,k).flat();for(const v of lines[k]){R.push(v);go(earlier.filter(w=>N[v][w]),R);R.pop();}}}go(S,[]);return best;}
let last=new Set([0]);for(let k=2;k<=K;k++){let now=new Set(),ct=Array(k).fill(0),mx=Array(k).fill(0),att=Array(k).fill(null),edges=sv[k-1].concat([Array(k-1).fill(0)]);let ni=0;
 for(const old of last){let A=decode(old,k-1);for(const e of edges){let B=A.map((r,i)=>r.concat(e[i])).concat([e.concat(2)]),c=canon(B);if(now.has(c))continue;now.add(c);let data=adjug(B);if(!data)continue;let[D,J,neg]=data;ct[neg]++;
 if(!neg)continue;
 let V=[],W=[];for(const w of sv[k]){let v=J.map(row=>dot(row,w));if(dot(v,w)===2*D){V.push(v);W.push(w);}}
 if(V.length+k<=mx[neg])continue;
 let N=V.map((v,i)=>W.map((w,j)=>{let d=dot(v,w);return i!==j&&(d===0||Math.abs(d)===Math.abs(D));})),C=clique(N);if(k+C.length>mx[neg]){mx[neg]=k+C.length;att[neg]=[canon(B),B,C.map(i=>W[i])];}
 }ni++;}
 const want=allmax[k];if(!want.every((v,j)=>v===mx[j+1])||mx.slice(1+want.length).some(x=>x)||burn(k)!==now.size)throw Error('census assertion');
 for(let i=1;i<att.length;i++)if(att[i]){const [,B,S]=att[i],[D,J,ni]=adjug(B);if(ni!==i||k+S.length!==mx[i])throw Error('witness count');for(let j=0;j<S.length;j++){let v=J.map(row=>dot(row,S[j]));if(dot(v,S[j])!==2*D)throw Error('norm');for(let l=0;l<j;l++){const t=dot(v,S[l]);if(t!==0&&Math.abs(t)!==Math.abs(D))throw Error('pair');}}}
 console.log(JSON.stringify({rank:k,basisOrbits:now.size,nonsingularByNegativeIndex:ct,indefiniteMaxima:mx.slice(1,1+want.length)}));last=now;}
