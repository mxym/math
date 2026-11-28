
"use strict";
// All powers in this table are exact below LIM. The same table is used
// by every shard; startup verifies it against BigInt.
const HALF=2**50, LIM=2**52, POW5=[1];
for(let k=1;k<=22;k++) POW5.push(5*POW5[k-1]);
if(POW5.some((v,k)=>BigInt(v)!==5n**BigInt(k))) throw Error("power table");
function v2n(x) {
    let w=x>>>0;
    if(w!==0) return 31-Math.clz32(w&-w);
    w=(x/2**32)>>>0;
    return 63-Math.clz32(w&-w);
}
function v2b(x) {
    let j=0n;
    while ((x&4294967295n)===0n) {x>>=32n;j+=32n;}
    return j+BigInt(v2n(Number(x&4294967295n)));
}
function nextBig(x) {
    const y=3n*x+1n,k=v2b(y);
    const peak=((y>>k)*5n**k-1n)/3n;
    const next=peak>>v2b(peak);
    return next<=BigInt(HALF)?Number(next):next;
}
function nextOddMinimum(x) {
    if(typeof x==="number"&&x<=HALF) {
      const y=3*x+1,k=v2n(y);
      if(k<POW5.length) {
        const z=(y/2**k)*POW5[k];
        if(z<=LIM) {
          const peak=(z-1)/3;
          return peak/2**v2n(peak);
        }
      }
    }
    return nextBig(BigInt(x));
}
function brute(x) {
   let n=BigInt(x);
   while(n&1n) n=(5n*n+1n)>>1n;
   while(!(n&1n)) n>>=1n;
   return n;
}
function verifyKernel() {
   let L=0;
   for(let v=1;v<=65539;v+=2) {
      const a=nextOddMinimum(v),b=brute(v);
      if(BigInt(a)!==b) throw Error("kernel "+v);
      L++;
   }
   for(let k=1;k<=140;k++) for(let j=0;j<9;j++) {
      const z=(1n<<BigInt(k+2))+2n*BigInt(j)+1n;
      if(BigInt(nextOddMinimum(z))!==brute(z)) throw Error("large kernel "+z);
      L++;
      // Find the odd x with 3*x+1 of valuation exactly k.
      const h=(1n<<BigInt(k))*(k%2===0?1n:5n);
      const target=(h-1n)/3n;
      if(target>0n&&(target&1n)===1n&&3n*target+1n===h) {
          if(BigInt(nextOddMinimum(target))!==brute(target)) throw Error("high valuation "+target);
          L++;
      }
   }
   console.log("exact mixed-kernel checks",L);
}
function check(minimum,maximum,m) {
    const seen=new Map(); let total=0;
    for(let x=minimum;x<=maximum;x+=2) {
       let y=x;
       for(let j=1;j<=m;j++) {
         y=nextOddMinimum(y);
         if(y<=x) {
           if(y===x) seen.set(x,j);
           break;
         }
       }
       total++;
       if((x&0xffffff)===0xffffff) console.log("shard",minimum,"through",x,"odds",total);
    }
    console.log("scan",minimum,maximum,m,total,JSON.stringify([...seen]));
    if(total!==(maximum-minimum)/2+1) throw Error("wrong count");
    const expected=[[1,1],[13,1],[17,2]].filter(([x])=>minimum<=x&&x<=maximum);
    if(JSON.stringify([...seen])!==JSON.stringify(expected)) throw Error("unexpected cycle minima");
}
const arg=process.argv[2];
if(arg==="--kernel-only") {
    verifyKernel();
} else {
    const shard=Number(arg);
    if(arg===undefined||!Number.isInteger(shard)||shard<0||shard>7)
        throw Error("choose a shard 0..7 (or --kernel-only)");
    if(shard===0) verifyKernel();
    check(shard*2**26+1,(shard+1)*2**26-1,21);
}
