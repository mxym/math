"use strict";
const N=2**29, LIMIT=2**50;
function directBig(x) {
  while ((x&1n)===1n) x=(5n*x+1n)/2n;
  do { x/=2n; } while ((x&1n)===0n);
  return x<=BigInt(LIMIT)?Number(x):x;
}
function following(x) {
  if (typeof x==="bigint") return directBig(x);
  for (;;) {
    if (x>LIMIT) return directBig(BigInt(x));
    x=(5*x+1)/2;
    if ((x&1)===0) break;
  }
  do { x/=2; } while ((x&1)===0);
  return x;
}
const shard=Number(process.argv[2]);
const W=2**26, a=shard*W+1, b=(shard+1)*W;
const found=[];
let count=0;
for (let x=a;x<b;x+=2) {
  let cur=x;
  for (let m=1;m<=21;m++) {
    cur=following(cur);
    if (cur<=x) {
      if (cur==x) found.push([x,m]);
      break;
    }
  }
  count++;
}
if (count!==W/2) throw Error("count");
const expected=shard===0?[[1,1],[13,1],[17,2]]:[];
if(JSON.stringify(found)!==JSON.stringify(expected)) throw Error("cycle mismatch");
console.log("independent direct-step shard",shard,a,b-1,count,JSON.stringify(found));