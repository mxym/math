'use strict';
// Exact enumeration in tiny Construction A instances; no lattice search routine.
let checks=0;
function yes(x){checks++;if(!x)throw Error("check failed")}
const wt=x=>{let k=0;while(x){x&=x-1;k++;}return k;};
function bin(n,k){let a=1n;for(let i=1;i<=k;i++)a=a*BigInt(n-i+1)/BigInt(i);return a;}
function brute(n,k) {
 const out=Array(n+1).fill(0n),powers=[1];
 for(let j=1;j<n;j++)powers[j]=powers[j-1]^(powers[j-1]<<1);
 const c=[0];
 for(let j=k;j<n;j++){const m=c.length;for(let i=0;i<m;i++)c.push(c[i]^powers[j]);}
 for(const x of c)out[wt(x)]++;
 return out;
}
function recur(n,k) {
 if(n===1)return k===0?[1n,1n]:[1n,0n];
 const m=n/2,out=Array(n+1).fill(0n);
 if(k>=m){
  const small=recur(m,k-m);
  small.forEach((v,w)=>out[2*w]=v);
 }else{
  const small=recur(m,k);
  small.forEach((v,w)=>{for(let j=0;j<=m-w;j++)out[2*j+w]+=v*bin(m-w,j)*2n**BigInt(w);});
 }
 return out;
}
for(const n of [1,2,4,8,16]){
 for(let k=0;k<=n;k++){
  const want=brute(n,k),have=recur(n,k);
  for(let j=0;j<=n;j++)yes(want[j]===have[j]);
  yes(want.reduce((s,v)=>s+v,0n)===2n**BigInt(n-k));
  if(k>=1&&k<=n/2){
   let a=1;while(a<k)a*=2;
   yes(want[1]===0n);
   yes(want[2]===BigInt(a)*bin(n/a,2));
  }
  if(k>n/2&&n>=2){
   yes(want[2]===0n);
   let expected=2n*BigInt(n),j=k-n/2;
   if(j<=n/4){
    let b=1;while(b<j)b*=2;
    expected+=16n*BigInt(b)*bin(n/(2*b),2);
   }
   yes(2n*BigInt(n)+16n*(want[4]||0n)===expected);
  }
 }
}
console.log({exactWeightEnumerationChecks:checks});
