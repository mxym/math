const fs = require("node:fs");
function rawShapes(p,a){
 let universe=[['']];for(let e=1;e<=a;e++)universe[e]=universe[e-1].flatMap(s=>Array.from({length:p},(_,i)=>s+i));
 const seen=new Set,counts=Array(a+1).fill(0);
 const lcp=(s,t)=>{let i=0;while(i<s.length&&i<t.length&&s[i]===t[i])i++;return i;};
 function next(k,A,X){
   counts[k]++;
   if(k===a){seen.add(X);return;}
   for(const w of universe[k+1]){
    if(A.some(t=>w.startsWith(t)))continue;
    let s=X;for(const t of A)s+=lcp(t,w);A.push(w);next(k+1,A,s);A.pop();
   }
 }
 next(1,['0'],'');return {counts,seen:[...seen].sort()};
}
function key(A){let s='';for(let j=0;j<A.length;j++)for(let i=0;i<j;i++){let k=0;while(k<A[i].length&&A[i][k]===A[j][k])k++;s+=k;}return s;}
if(process.argv.length!==3)throw Error("Usage: node verifier.js schedule.json");
const D=JSON.parse(fs.readFileSync(process.argv[2],"utf8"));
const expected=[[3,4],[3,5],[5,3]].map(([p,a])=>rawShapes(p,a));
function K(s){return JSON.stringify([...s].sort());}
const comb=a=>Array.from({length:a},(_,i)=>'0'.repeat(i)+'2');
const base5=expected[2].seen;
for(let j=0;j<2;j++){
const raw=new Set(expected[j].seen.flatMap(k=>base5.map(v=>k+'|'+v)));
const small=comb(j+4),c5=['4','04','004'];
const absent=key(small)+'|'+key(c5);
if(!raw.delete(absent))throw Error("missing comb");
const cert=D.filter(o=>o.profile===j).map(o=>o.excluded.map(key).join('|'));
if(K(raw)!==K(cert))throw Error("bad coverage");
}
console.log(JSON.stringify(expected));
