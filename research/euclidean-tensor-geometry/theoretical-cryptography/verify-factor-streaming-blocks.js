"use strict";
// Finite counting certificate on generated small-prime pools only.
const ok=(b,m)=>{if(!b)throw Error(m);};
const binom=(n,k)=>{let z=1n;if(k<0||k>n)return 0n;for(let i=0;i<k;i++)z=z*BigInt(n-i)/BigInt(i+1);return z;};
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
let pools=0,edges=0,localPatternChecks=0,scheduleIdentities=0,simulations=0,successfulRuns=0;
function span(n,r){
 let z=0n;for(let a=0;a<=n;a++){const x=binom(a+r-1,r-1)*binom(n-a+r-1,r-1);z+=x;}
 ok(z===binom(n+2*r-1,2*r-1), "schedule count"); scheduleIdentities++;
}
for(let n=4;n<=11;n++){
 const P=2**(n-1), S=Array.from({length:P},(_,i)=>i+P).filter(prime);
 const G=[new Map(),new Map()], E=[];
 for(let i=0;i<S.length;i++)for(let j=i+1;j<S.length;j++){
  const p=S[i],q=S[j],N=p*q,blocks=[Math.floor(N/P),N%P];
  for(let b=0;b<2;b++){const x=blocks[b];if(!G[b].has(x))G[b].set(x,new Set());
   const L=G[b].get(x);ok(!L.has(p)&&!L.has(q),"label repeated at vertex");L.add(p);L.add(q);}
  E.push({p,q,blocks});edges++;
 }
 ok(G[0].size<=3*P&&G[1].size<=P/2,"vertex counts");
 for(let r=1;r<=10;r++)span(n,r);
 if(n<=8)for(let side=0;side<2;side++)for(const L of G[side].values())for(let mask=0;mask<2**n;mask++){
  const h=mask.toString(2).split("1").length-1, F=new Map();
  for(const p of L){const tag=p&mask, count=(F.get(tag)||0)+1;ok(count<=2**(n-h),"pattern capacity");F.set(tag,count);}
  localPatternChecks++;
 }
 const W=Array(n+1).fill(0);
 for(let k=1;k<=n;k++){const f=new Map();for(const p of S){const tag=p>>(n-k);f.set(tag,(f.get(tag)||0)+1);}
  W[k]=Math.max(...f.values());}
 for(let r=1;r<=3;r++)for(let s=0;s<=3;s++)for(let initial=0;initial<2;initial++)for(let seed=0;seed<4;seed++){
  let totals=0, byTime=new Map(), shortLong=Array.from({length:n+1},()=>[0,0]);
  for(const {p,q,blocks} of E){
   let u=0,out="",tf=[],lengths=[],a=0;
   for(let j=0;j<2*r;j++){
    const side=(initial+j)%2,x=blocks[side],ls=Array.from(G[side].get(x)).sort((a,b)=>a-b);
    const label=ls[(u+seed+j)%ls.length].toString(2);
    const k=(j===2*r-1)?n-Math.min(2*r-1,n):Number((x+3*u+seed+j)%3!==0);
    const piece=j===2*r-1?(k===0 ? "" : label.slice(-k)):label.slice(j,j+k);
    lengths.push(piece.length);if(side===0)a+=piece.length;out+=piece;
    if(j<2*r-1){u=((x^((seed+2)*u))+(x>>>2)+j)%(2**s);tf.push(u);}
   }
   if(out!==p.toString(2)&&out!==q.toString(2))continue;
   totals++;
   const key=tf.join(":")+";"+lengths.join(":");
   const T=byTime.get(key)||{a,count:0,h:new Map(),l:new Map()};T.count++;byTime.set(key,T);
   T.h.set(blocks[0],(T.h.get(blocks[0])||0)+1);
   T.l.set(blocks[1],(T.l.get(blocks[1])||0)+1);
   if(r===1)for(let k=1;k<=n;k++)shortLong[k][Number(lengths[0]>=k)]++;
  }
  for(const T of byTime.values()){
   ok(Math.max(...T.h.values())<=2**(n-T.a)&&Math.max(...T.l.values())<=2**T.a,"per-block capacity");
   ok(T.count<=Math.min(G[0].size*2**(n-T.a),G[1].size*2**T.a),"schedule capacity");
  }
  if(r===1)for(let k=1;k<=n;k++){
   ok(shortLong[k][1]<=G[initial].size*W[k], "long early output");
   ok(shortLong[k][0]<=G[1-initial].size*(2**s)*(2**k-1),"short early output");
  }
  let countBound=0n;
  for(let a=0;a<=n;a++)countBound+=binom(a+r-1,r-1)*binom(n-a+r-1,r-1)*BigInt(Math.min(G[0].size*2**(n-a),G[1].size*2**a));
  ok(BigInt(totals)<=countBound*2n**BigInt((2*r-1)*s),"total");
  successfulRuns+=totals;simulations++;
 }
 pools++;
}
ok(successfulRuns>0,"nonzero sample");
console.log({pools,edges,localPatternChecks,scheduleIdentities,simulations,successfulRuns});