'use strict';
// Rational bounds and exact equivariance of a toy Markov table on finite cyclic groups.
let checks=0;
function yes(x){checks++;if(!x)throw Error('check failed');}
yes(51n*64n*4n===256n*17n*3n);
yes(51*5<256);
yes(32n*16n<5n**4n);
yes(3n*8192n*50n/4n-33n*50n>37n*8192n);
yes(119n*1024n>97n*1250n);
yes(2n**18n < 2n*(2n**18n-1n));
for(const [N,q] of [[8,4],[12,3],[15,5],[30,6]]){
 const domain=Array.from({length:N},(_,i)=>i);
 const H=Array.from({length:q},(_,i)=>i*N/q);
 const K=domain.map(x=>domain.map(y=>BigInt((y+x*x+3*x)%N+1)));
 const norm=BigInt(N*(N+1)/2);
 const sym=domain.map(x=>domain.map(y=>H.reduce((s,h)=>s+K[(x+h)%N][(y+h)%N],0n)));
 for(const x of domain){
  yes(sym[x].reduce((s,a)=>s+a,0n)===BigInt(q)*norm);
  for(const y of domain)for(const h of H)yes(sym[(x+h)%N][(y+h)%N]===sym[x][y]);
 }
 const prior=domain.map(x=>BigInt(1+(7*x*x+3*x)%11));
 for(const y of domain){
  const direct=domain.reduce((s,x)=>s+prior[x]*sym[x][y],0n);
  const averaged=H.reduce((s,h)=>s+domain.reduce((u,x)=>u+prior[(x+N-h)%N]*K[x][(y+h)%N],0n),0n);
  yes(direct===averaged);
 }
}
console.log({exactSyntheticChecks:checks});
