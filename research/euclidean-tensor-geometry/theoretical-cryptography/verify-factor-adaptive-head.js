"use strict";
// Generated tiny arithmetic labels and abstract local rules; no factorizer.
const must=(x,m)=>{if(!x)throw Error(m);};
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
const choose=(n,k)=>{let r=1n;for(let j=0;j<k;j++)r=r*BigInt(n-j)/BigInt(j+1);return r;};
let degreeChecks=0,groups=0,adaptiveModels=0,poolEdges=0,verifiedSuccesses=0;
for(let n=4;n<=9;n++){
 const P=2**(n-1),S=Array.from({length:P},(_,i)=>P+i).filter(prime), es=[];
 for(let i=0;i<S.length;i++)for(let j=i+1;j<S.length;j++)es.push([S[i]*S[j],S[i],S[j]]);
 poolEdges+=es.length;
 for(let k=1;k<2*n;k++){
  const B=2**k,V=[2**(2*n-k),B], d=k-(n-1),D=[2**Math.max(0,d),2**Math.max(0,-d)];
  const G=[new Map(),new Map()];
  for(const [N,p,q] of es){
   const views=[Math.floor(N/B),N%B];
   for(let i=0;i<2;i++){
    if(!G[i].has(views[i]))G[i].set(views[i],new Map());
    const L=G[i].get(views[i]);
    for(const t of [p,q]){const c=(L.get(t)||0)+1;L.set(t,c);must(c<=D[i],"cut degree");degreeChecks++;}
   }
  }
  const powcap=2n**BigInt(3*n+Math.abs(d));
  for(let seed=0;seed<10;seed++){
   const tags=1+seed%3, states=(n+1)*tags, s=Math.ceil(Math.log2(states));
   const byClass=new Map(), counts=Array(n+1).fill(0);
   for(const [N,p,q] of es){
    const views=[Math.floor(N/B),N%B], transcript=[], schedule=[];
    let written=0,g=0,out="",j=0,a=0;
    for(;;){
     const side=(j+seed)%2,v=views[side], local=Array.from(G[side].get(v).keys()).sort((a,b)=>a-b);
     const label=local[(seed+g+written)%local.length].toString(2);
     // Each visit either stops and writes a suffix or writes exactly one bit,
     // changes its stored configuration, and crosses the cut.
     const quit=written>=n||(v+19*g+7*written+seed)%4===0;
     const piece=quit?label.slice(written):label.slice(written,written+1);
     schedule.push(piece.length);if(side===0)a+=piece.length;out+=piece;
     if(quit)break;
     written++;g=((v^(g+seed))+written)%tags;
     transcript.push(written*tags+g);j++;
    }
    if(out!==p.toString(2)&&out!==q.toString(2))continue;
    counts[j]++;const key=transcript.join(":")+";"+schedule.join(":");
    const z=byClass.get(key)||{a,c:0};must(z.a===a,"schedule sum");z.c++;byClass.set(key,z);
   }
   for(const {a,c} of byClass.values()){
    must(c<=Math.min(V[0]*D[0]*2**(n-a),V[1]*D[1]*2**a),"crossing-schedule capacity");
    must(BigInt(c)**2n<=powcap,"geometric-mean capacity");groups++;
   }
   let covered=0n,Bsum=0n;
   for(let h=0;h<=n;h++){
    covered+=BigInt(counts[h]);Bsum+=2n**BigInt(h*s)*choose(n+h,h);
    must(covered**2n<=powcap*Bsum**2n,"cumulative few crossings");
   }
   verifiedSuccesses+=counts.reduce((a,b)=>a+b,0);adaptiveModels++;
  }
 }
}
must(verifiedSuccesses>0,"missing success coverage");
console.log({poolEdges,degreeChecks,groups,adaptiveModels,verifiedSuccesses});