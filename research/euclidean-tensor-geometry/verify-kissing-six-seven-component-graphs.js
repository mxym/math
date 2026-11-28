'use strict';
// Scan every edge subset, retain triangle-free, alpha<=3, factor-critical; quotient only by explicit permutations.
const n=7,E=[],idx=Array.from({length:n},()=>[]);for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){idx[i][j]=idx[j][i]=1<<E.length;E.push([i,j])}
function perm(A){if(!A.length)return [[]];return A.flatMap(i=>perm(A.filter(v=>v!==i)).map(p=>[i,...p]));}
const all=perm([0,1,2,3,4,5,6]),C4=Array.from({length:128},(_,i)=>i).filter(x=>x.toString(2).replaceAll('0','').length==4),tri=[],abs=[];for(let i=0;i<7;i++)for(let j=i+1;j<7;j++)for(let k=j+1;k<7;k++)tri.push(idx[i][j]|idx[i][k]|idx[j][k]);for(const b of C4)abs.push(E.reduce((z,[i,j],k)=>z+((b>>i&1)&&(b>>j&1)?1<<k:0),0));
function pair(x,S){if(!S)return true;let v=Math.clz32(S)^31,Z=S^(1<<v);for(let i=0;i<n;i++)if((Z>>i&1)&&(x&idx[i][v])&&pair(x,Z^(1<<i)))return true;return false}
function pm(x,p){return E.reduce((s,[i,j],k)=>s+((x>>k&1)?idx[p[i]][p[j]]:0),0)}
const seen=new Uint8Array(1<<21);let count=0,labelled=0;const expected=[[42232,1260],[44336,360],[44340,2520],[44404,2520],[44856,1260],[61112,630]];for(let x=0;x<1<<21;x++){if(seen[x]||tri.some(m=>(m&x)==m)||abs.some(m=>(m&x)==0)||Array.from({length:7},(_,i)=>i).some(v=>!pair(x,127^(1<<v))))continue;
const possible=new Set(all.map(p=>pm(x,p)));for(let a of possible)seen[a]=1;
const cyc=all.find(p=>p.every((j,i)=>x&idx[j][p[(i+1)%7]]));let chords=cyc?E.filter(([i,j])=>j-i!==1&&j-i!==6&&(x&idx[cyc[i]][cyc[j]])):null;
if(x!==expected[count]?.[0]||possible.size!==expected[count]?.[1])throw Error('different class');console.log('class',x,'orbit',possible.size,'chords',JSON.stringify(chords));labelled+=possible.size;count++}
if(count!==6||labelled!==8550)throw Error('different census');console.log('PASS all 2^21 labelled graphs; six orbits on 8550 admissible labellings.');
