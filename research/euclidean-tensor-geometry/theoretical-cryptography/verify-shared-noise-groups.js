'use strict';
// Exact synthetic mixture tables. No Ring-LWE samples, schemes or secrets.
let checks=0;
function assert(a,b){checks++;if(a!==b)throw Error(a+' != '+b);}
const pow=(x,m)=>x**BigInt(m);
for(const [pi,c] of [[[1n,1n],[1n,-1n]],[[1n,2n],[2n,-1n]]]){
 const ptotal=pi[0]+pi[1];
 const w=c.map(t=>[4n-t,4n+t]); // component probabilities w/8; reference q is uniform
 assert(pi[0]*w[0][1]+pi[1]*w[1][1],4n*ptotal);
 for(let m=1;m<=10;m++){
  let probSq=0n,probMass=0n;
  for(let bits=0;bits<2**m;bits++){
   let p=0n;
   for(let s=0;s<2;s++){
    let n=pi[s];
    for(let j=0;j<m;j++)n*=w[s][(bits>>j)&1];
    p+=n;
   }
   probSq+=p*p;probMass+=p;
  }
  assert(probMass,ptotal*pow(8n,m));
  let pairTotal=0n;
  for(let i=0;i<2;i++)for(let j=0;j<2;j++)pairTotal+=pi[i]*pi[j]*pow(16n+c[i]*c[j],m);
  // Prob squared is over denominator (ptotal*8^m)^2, reference uniform.
  assert(probSq*pow(2n,m)*pow(16n,m),pairTotal*pow(8n,2*m));
  if(m===1)assert(pairTotal,ptotal*ptotal*pow(16n,m));
  if(m===2){
   const weightedSecond=pi[0]*c[0]**2n+pi[1]*c[1]**2n;
   assert(pairTotal-ptotal*ptotal*pow(16n,m),weightedSecond**2n);
  }
 }
}
console.log({exactSyntheticChecks:checks});
