// Standalone exact E6 incidence-block decomposition. Run: node this-file.js
'use strict';
const ix=[0,1,2,3,4,5],G=ix.map(i=>ix.map(j=>i===j?2:((i<5&&j<5&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===5))?-1:0));const dot=(a,b)=>a.reduce((s,t,i)=>s+t*b[i],0);
const roots=ix.map(i=>ix.map(j=>+(i===j))),known=new Set(roots.map(r=>r.join()));for(const r of roots)for(const i of ix){const s=r.slice();s[i]-=dot(r,G[i]);if(!known.has(s.join())){known.add(s.join());roots.push(s);}}
const T=roots.filter(v=>v.every(t=>t>=0));const P=T.map(r=>T.map(v=>dot(r,G.map(g=>dot(g,v)))));function det(A){let d=1,sg=1;const a=A.map(v=>v.slice());for(let i=0;i<a.length-1;i++){let k=i;while(k<a.length&&!a[k][i])k++;if(k===a.length)return 0;if(k!==i){[a[k],a[i]]=[a[i],a[k]];sg=-sg;}for(let j=i+1;j<a.length;j++)for(let l=i+1;l<a.length;l++){const v=(a[j][l]*a[i][i]-a[j][i]*a[i][l])/d;if(!Number.isSafeInteger(v))throw Error('det');a[j][l]=v;}d=a[i][i];}return sg*a.at(-1).at(-1);}
if(roots.length!==72||T.length!==36)throw Error("E6 generation");
const witness=[[1,0,0,0,0,0],[0,0,1,0,0,0],[0,0,0,0,1,0],[1,2,3,2,1,2]].map(w=>T.findIndex(v=>String(v)===String(w)));
if(witness.some(i=>i<0)||witness.some((i,k)=>witness.some((j,l)=>P[i][j]!==2*+(k===l))))throw Error("four orthogonal roots");
const masks=Array.from({length:64},(_,m)=>ix.filter(i=>m>>i&1));
const D=(a,m)=>det(masks[m].map(i=>masks[m].map(j=>P[a[i]][a[j]])));const pair=masks.map((v,i)=>v.length===2?i:0).filter(Boolean),trip=masks.map((v,i)=>v.length===3?i:0).filter(Boolean);
// After the fast pair/triple partitions, only a rank-five determinant test
// and the exact full-rank dependence test are required.
function classify(a){const nm=1<<a.length,full=nm-1;const adj=a.map((u,i)=>a.reduce((m,v,j)=>m|(i!==j&&P[u][v]?1<<j:0),0));const con3=m=>{let x=0;for(const i of masks[m])if(adj[i]&m)x++;return x===3;};const E=pair.filter(m=>m<nm&&adj[masks[m][0]]&m);
if(a.length===6){for(const u of E)for(const v of E)if(!(u&v)&&E.includes(full^u^v))return '222';for(const m of trip)if((m&1)&&con3(m)&&con3(full^m))return '33';}

if(a.length===6){for(let i=0;i<6;i++)if(D(a,full^(1<<i))===6)return '51';}
return D(a,full)===0?'dep':'residual';}
const h={};function visit(a,k){
 if(a.length<6){for(let i=k;i<=T.length-(6-a.length);i++)visit(a.concat([i]),i+1);return;}
 const label=classify(a);h[label]=(h[label]||0)+1;
}visit([],0);
const expected={'222':1781514,'33':62220,'51':46656,dep:57402};
if(Object.keys(h).length!==4||Object.entries(expected).some(([l,n])=>h[l]!==n))throw Error('E6 decomposition failed: '+JSON.stringify(h));
console.log(h);