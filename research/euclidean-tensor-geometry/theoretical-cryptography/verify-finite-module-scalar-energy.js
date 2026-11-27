function cert(q,B,D,E,w) {
 const mod=x=>(x%q+q)%q,gcd=(a,b)=>b?gcd(b,a%b):a,L=q**B,mats=L**D;
 const V=[]; function pick(c,e,k){if(c.length===B){if(k&&c.reduce((g,x)=>gcd(g,Math.abs(x)),0)===1&&c.find(x=>x)!==undefined&&c.find(x=>x)>0)V.push(c);return} const m=Math.floor(Math.sqrt(E-e));for(let x=-m;x<=m;x++)if(k+(x!==0)<=w)pick(c.concat(x),e+x*x,k+(x!==0));}pick([],0,0);
 const lines=new Set(V.map(c=>{const a=mod(c.find(x=>x!==0));let s=1;while(mod(a*s)!==1)s++;return c.map(x=>mod(x*s)).join(",")}));if(lines.size!==V.length)throw Error("modular projective collision");
 const rows=Array.from({length:L},(_,i)=>Array.from({length:B},(_,j)=>Math.floor(i/q**j)%q));const zero=rows.map(row=>V.map(c=>mod(c.reduce((s,x,j)=>s+x*row[j],0))===0));
 let sum=0,sum2=0,success=0,counts=Array(V.length).fill(0);
 for(let z=0;z<mats;z++){const ids=Array.from({length:D},(_,i)=>Math.floor(z/L**i)%L);let hits=0;for(let i=0;i<V.length;i++)if(ids.every(k=>zero[k][i])){hits++;counts[i]++;}if(hits)success++;sum+=hits;sum2+=hits*hits;}
 const N=V.length, pnum=mats/q**D, jnum=mats/q**(2*D);
 if(counts.some(x=>x!==pnum)||sum!==N*pnum||sum2!==sum+N*(N-1)*jnum)throw Error("moment mismatch");
 return {q,B,D,E,w,mats,N,sum,sum2,success,signedUnit:V.filter(c=>c.every(x=>Math.abs(x)<=1)).length};
}
const result=[cert(5,4,1,4,4),cert(7,3,2,5,3)];
console.log(JSON.stringify(result));
