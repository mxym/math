"use strict";
// Exact finite source-law checks only. No untrusted modulus is factored.
const assert=(b,m)=>{if(!b)throw Error(m);};
const prime=x=>{for(let d=2;d*d<=x;d++)if(x%d===0)return false;return x>=2;};
const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a;};
const lcm=(a,b)=>a/gcd(a,b)*b;
let regularCases=0,partitionCases=0,classChecks=0,tailLevels=0;
for(let n=5;n<=9;n++){
 const P=2**(n-1),S=Array.from({length:P},(_,i)=>P+i).filter(prime),M=S.length;
 assert(new Set(S.flatMap((p,i)=>S.slice(i+1).map(q=>p*q))).size===M*(M-1)/2,"toy products collide");
 for(let d=1;d<M-1;d++){
  if(M*d%2)continue;
  const e=BigInt(M*d),f=BigInt(M*(M-1-d)),N=e+f,T=23n,mass=7n,D=T*e*f;
  const inE=(i,j)=>{
   if(i===j)return false;let k=(j+M-i)%M;k=Math.min(k,M-k);
   return k<=Math.floor(d/2)||(d%2&&k===M/2);
  };
  const W=(i,j)=>i===j?0n:inE(i,j)?mass*f:(T-mass)*e;
  let total=0n,cntA=0n,actualA=0n;
  for(let i=0;i<M;i++){
   let row=0n,num=0;
   for(let j=0;j<M;j++){
    const w=W(i,j);assert(w===W(j,i),"symmetry");row+=w;
    if(inE(i,j)){num++;cntA++;actualA+=w;assert(w*N*e*T===mass*N*D,"inside likelihood");}
    else if(i!==j)assert(w*N*f*T===(T-mass)*N*D,"outside likelihood");
   }
   total+=row;assert(row*BigInt(M)===D&&num===d,"endpoint/conditional two-level law");
  }
  assert(total===D&&cntA===e&&actualA*T===D*mass,"regular mixture event");
  regularCases++;
 }
 for(let k=1;k<=Math.min(M,8);k++)for(let seed=0;seed<5;seed++){
  const groups=Array.from({length:k},()=>[]);
  for(let i=0;i<M;i++)groups[((i^seed)+13*(seed+1))%k].push(i);
  const C=groups.filter(g=>g.length),K=C.length;
  let L=1n;
  for(let i=0;i<K;i++)for(let j=0;j<K;j++){
   const a=BigInt(C[i].length),b=BigInt(C[j].length);
   L=lcm(L,i===j?2n*a:lcm(a,b));
  }
  const W=Array.from({length:M},()=>Array(M).fill(0n));
  for(let i=0;i<K;i++)for(let j=0;j<K;j++){
   const a=C[i].length,b=C[j].length;
   if(i!==j){
    const grid=Number(lcm(BigInt(a),BigInt(b))),unit=BigInt(a*b)*(L/BigInt(grid));
    for(let t=0;t<grid;t++)W[C[i][Math.floor(t*a/grid)]][C[j][Math.floor(t*b/grid)]]+=unit;
   } else if(a>1){
    const unit=BigInt(a-1)*L/2n;
    for(let t=0;t<a;t++)for(const shift of [-1,1])
     W[C[i][t]][C[i][(t+a+shift)%a]]+=unit;
   }
  }
  let supported=0;
  for(let i=0;i<K;i++)for(const p of C[i]){
   assert(W[p][p]===0n,"diagonal chosen");
   for(let j=0;j<K;j++){
    let s=0n;
    for(const r of C[j]){
      assert(W[p][r]===W[r][p],"quantile symmetry");s+=W[p][r];
      if(W[p][r]>0n)supported++;
    }
    assert(s===BigInt(C[j].length-Number(i===j))*L,"conditional class exact");
    classChecks++;
   }
   assert(W[p].reduce((x,y)=>x+y,0n)===BigInt(M-1)*L,"uniform marginals");
  }
  assert(supported<=2*K*M,"sparse class support");
  partitionCases++;
 }
}
for(let n=2;n<=7;n++)for(let J=1;J<=4;J++){
 const B=BigInt(n),m=8n*B**BigInt(2*J)+1n;
 const T=2n*B**BigInt(J);
 const tot=Array.from({length:J},(_,j)=>T/(2n*B**BigInt(j+1))).reduce((x,y)=>x+y,0n);
 let used=0n;
 for(let j=1;j<=J;j++){
  const NN=B**BigInt(j),d=2n*((m-1n)/(2n*NN**2n)),w=T/(2n*NN);
  const num=(T-tot)*d+w*(m-1n),den=T*d;
  assert(d>0n&&2n*num>=NN*den&&num<=2n*NN*den,"likelihood layer");
  used+=d;tailLevels++;
 }
 assert(used<m-2n&&tot<T,"disjoint layer capacity");
}
console.log({regularCases,partitionCases,classChecks,tailLevels});