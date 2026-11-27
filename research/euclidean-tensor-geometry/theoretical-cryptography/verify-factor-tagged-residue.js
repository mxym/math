"use strict";
// Finite counting in locally generated tiny pools; no supplied-integer factoring routine.
const must=(x,m)=>{if(!x)throw Error(m);};
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a;};
const lcm=(a,b)=>a/gcd(a,b)*b;
function powers(m){
 const R=[];for(let d=2;d*d<=m;d++)if(m%d===0){let a=1;while(m%d===0){a*=d;m/=d;}R.push([d,a]);}
 if(m>1)R.push([m,m]);return R;
}
let families=0,tagCoverageChecks=0,weightTables=0,finiteCollisions=0,unitErrorCollisions=0;
for(let n=5;n<=9;n++){
 const P=2**(n-1),S=Array.from({length:P},(_,i)=>P+i).filter(prime),Xs=[];
 for(let i=0;i<S.length;i++)for(let j=i+1;j<S.length;j++)Xs.push(BigInt(S[i]*S[j]));
 for(let U=2;U<=7;U++)for(let seed=0;seed<14;seed++){
  // Families include composite tags, several powers of one prime, and base-absorbed tags.
  const M=Array.from({length:6+seed},(_,i)=>2+((i*13+i*i+7*seed)%(U*U+seed+3)));
  const mods=[...new Set(M)].sort((a,b)=>a-b),D=mods.reduce((a,b)=>a+b,0);
  let L=1n;for(let m=2;m<=U;m++)L=lcm(L,BigInt(m));
  for(const m of mods)if(m>U*U)L=lcm(L,BigInt(m));
  const groups=new Map(), tagAt=new Map();
  for(const m of mods){
   const large=m>U*U?[]:powers(m).filter(([,a])=>a>U);
   must(large.length<=1,"two large components");
   if(!large.length){must(L%BigInt(m)===0n,"base misses tag");tagCoverageChecks++;continue;}
   const [p,a]=large[0];groups.set(p,Math.max(groups.get(p)||0,a));tagAt.set(m,p);
  }
  const G=[...groups.entries()],J=G.length, cost=G.reduce((s,[,a])=>s+a,0);must(cost<=D,"group budget");
  for(const [m,p] of tagAt){must(lcm(L,BigInt(groups.get(p)))%BigInt(m)===0n,"group does not cover tag");tagCoverageChecks++;}
  const e=Array(J+1).fill(0n);e[0]=1n;
  for(const [,a] of G)for(let k=J;k>=1;k--)e[k]+=BigInt(a)*e[k-1];
  let fact=1n;
  for(let k=0;k<=J;k++){
   if(k>0)fact*=BigInt(k);
   must(e[k]*fact<=BigInt(D)**BigInt(k),"symmetric product cap");
   if(L*e[k]>=BigInt(Xs.length))continue;
   for(let tweak=0;tweak<3;tweak++){
    const table=new Map();let successes=0;
    for(const X of Xs){
      const W=new Map(mods.map((m,i)=>[m,1+Number(((X^BigInt((xmix(tweak,i)+seed)*m))*BigInt(i+3))%59n)]));
      const gweights=new Map(G.map(([p])=>[p,0]));
      for(const [m,p] of tagAt)gweights.set(p,gweights.get(p)+W.get(m));
      const tops=G.slice().sort(([a],[b])=>gweights.get(b)-gweights.get(a)||a-b).slice(0,k).sort(([a],[b])=>a-b);
      const key=tops.map(([p,a])=>[p,String(X%BigInt(a))].join("/")).join(";")+"@"+String(X%L);
      if(table.has(key)){
       const Y=table.get(key);must(X!==Y,"distinct products");
       const baseMass=mods.filter(m=>!tagAt.has(m)).reduce((s,m)=>s+W.get(m),0);
       const expectedMass=baseMass+tops.reduce((s,[p])=>s+gweights.get(p),0);
       const actual=mods.filter(m=>(X-Y)%BigInt(m)===0n).reduce((s,m)=>s+W.get(m),0);
       const tot=mods.reduce((s,m)=>s+W.get(m),0);
       must(actual>=expectedMass&&actual*J>=k*tot,"weighted collision");
       if(k===J){must(actual===tot,"unit error");unitErrorCollisions++;}
       successes++;finiteCollisions++;
      } else table.set(key,X);
    }
    must(BigInt(table.size)<=L*e[k]&&successes>0,"collision by tuples");
    weightTables++;
   }
  }
  families++;
 }
}
function xmix(a,b){return (a+3)*(b+5)^((a+b+7)*23);}
must(weightTables>0&&unitErrorCollisions>0,"missing finite cases");
console.log({families,tagCoverageChecks,weightTables,finiteCollisions,unitErrorCollisions});