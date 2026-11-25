'use strict';
function sets(s,k){return Array.from({length:1<<s},(_,x)=>Array.from({length:s},(_,i)=>i).filter(i=>(x>>i)&1)).filter(u=>u.length===k);}
function interlace(u,v,s){
 return Number(u.every((j,i)=>v.filter(t=>i+1<u.length?j<=t&&t<u[i+1]:t>=j||t<u[0]).length===1));
}
function expect(u,v,k) {
 // 2 times the determinant of the minor of rows T(w_j), scaled initially by two.
 const n=k,A=u.map(j=>v.map(c=>BigInt(2*Number(c>=j)-1)));
 return bareiss(A) / (2n**BigInt(n-1));
}
function bareiss(A){
 A=A.map(x=>x.slice());const n=A.length;let den=1n,sg=1n;
 if(!n)return 1n;
 for(let k=0;k<n-1;k++){
  let j=k;while(j<n&&A[j][k]===0n)j++;if(j===n)return 0n;
  if(j!==k){[A[k],A[j]]=[A[j],A[k]];sg=-sg;}
  const p=A[k][k];
  for(let i=k+1;i<n;i++)for(let j=k+1;j<n;j++){
   const num=A[i][j]*p-A[i][k]*A[k][j];
   if(num%den)throw Error('nonintegral Bareiss');
   A[i][j]=num/den;
  }
  for(let i=k+1;i<n;i++)A[i][k]=0n;
  den=p;
 }
 return sg*A[n-1][n-1];
}
const bin=(a,b)=>b<0||b>a?0:b===0?1:bin(a-1,b-1)+bin(a-1,b);
let comparisons=0;
for(let s=2;s<=9;s++){
 for(let k=2;k<=s;k+=2){
  const U=sets(s,k);
  const A=U.map(u=>U.map(v=>{
   const x=BigInt(interlace(u,v,s));
   if(x!==expect(u,v,k))throw Error('wedge identity mismatch');
   comparisons++;return x;
  }));
  const x=bareiss(A),h=2n**BigInt(bin(s-1,k));if(x!==h&&x!==-h)throw Error('even block determinant');
 }
}
console.log(JSON.stringify({comparisons,range:'s=2..9, even positive k'}));
