"use strict";
const n=6, E=[[1,2,3],[0,2,4],[0,3,4],[1,3,4],[2,3,4],[0,1,5],[0,2,5],[1,2,5],[1,3,5],[0,4,5]];
const edgeSet=new Set(E.map(t=>t.join(",")));
const pairs=[], quads=[];
for(let j=1;j<n;j++)for(let i=0;i<j;i++)pairs.push([i,j]);
for(let l=3;l<n;l++)for(let k=2;k<l;k++)for(let j=1;j<k;j++)for(let i=0;i<j;i++)quads.push([i,j,k,l]);
for(const q of quads) if(q.every((_,i)=>edgeSet.has(q.filter((_,j)=>j!==i).join(",")))) throw new Error("witness is not tetrahedron-free");
const A=Array.from({length:n},()=>Array(n).fill(0));
const newTriples=pairs.map(([i,j])=>E.filter(t=>t[1]===i&&t[2]===j));
const newQuads=pairs.map(([i,j])=>quads.filter(t=>t[2]===i&&t[3]===j));
function allowedTriple(T) {
    return T.every(x=>T.some(y=>A[x][y]!==0) && T.filter(y=>A[x][y]===1).length<=1);
}
function inducedDirectedFourCycle(T) {
    return T.every(x=>T.filter(y=>A[x][y]===1).length===1 && T.filter(y=>A[x][y]===-1).length===1);
}
let visited = 0;
function dfs(k) {
    visited++;
    if (k === pairs.length) return true;
    const [i,j]=pairs[k];
    for (const v of [-1,0,1]) {
        A[i][j]=v; A[j][i]=-v;
        if (newTriples[k].some(t=>!allowedTriple(t))) continue;
        if (newQuads[k].some(inducedDirectedFourCycle)) continue;
        if (dfs(k+1)) return true;
    }
    return false;
}
if (dfs(0)) throw new Error("witness has a Fon-der-Flaass completion");
console.log("Tetrahedron-free (6 vertices, 10 edges), no Fon-der-Flaass completion; checked search nodes:", visited);
