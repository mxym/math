'use strict';
// Exact finite sign checks for the dormant-degree estimate; not an asymptotic simulation.
const isPrime = n => n > 1 && Array.from({length:Math.max(0,Math.floor(Math.sqrt(n))-1)}, (_,i)=>i+2).every(p=>n%p);
let checks=0;
for(let q=3;q<50;q+=2) if(isPrime(q)){
  for(let J=2;J<=(q+1)/2;J++) for(let j=1;j<J;j++){
    // q^(-2j/J) < 1-j/J, after raising both sides to J.
    if(BigInt(q)**BigInt(2*j)*BigInt(J-j)**BigInt(J)<=BigInt(J)**BigInt(J)) throw Error('dormant-degree sign');
    checks++;
  }
}
console.log({checks});
