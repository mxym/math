"use strict";
// Fixed exact tests of the finite identities, not of asymptotic estimates.
let checks=0;
function test(x,why){++checks;if(!x)throw Error(why);}
const P=[2,3,5,7,11], period=2310, den=12n, D=den**5n;
const setups=[[1,3,7,9,12],[0,6,6,6,6],[8,11,5,0,12]];
for(const weights of setups){
  for(const [x,y] of [[0,17],[12,181],[111,77],[710,1300],[100000,81],[0,period+1]]){
    let actual=0n,l2=0n,l4=0n;
    for(let m=x+1;m<x+y;m++){
      const vals=P.map((p,i)=>m%p===0?BigInt(weights[i]):0n);
      const full=vals.reduce((a,v)=>a*(den-v),1n);
      let s2=0n,s4=0n;
      for(let mask=0;mask<(1<<P.length);mask++){
        let v=1n,k=0;
        for(let j=0;j<P.length;j++)if((mask>>j)&1){v*=vals[j];++k;}
        v*=den**BigInt(P.length-k);
        if(k%2)v=-v;
        if(k<=2)s2+=v;
        if(k<=4)s4+=v;
      }
      test(s2>=full&&s4>=full,"pointwise even Bonferroni");
      actual+=full;l2+=s2;l4+=s4;
    }
    const counts=[0n,0n,0n];
    for(let mask=0;mask<(1<<P.length);mask++){
      let p=1,v=1n,k=0;
      for(let j=0;j<P.length;j++)if((mask>>j)&1){p*=P[j];v*=BigInt(weights[j]);++k;}
      const count=Math.floor((x+y-1)/p)-Math.floor(x/p);
      test(Math.abs(count*p-y)<=p,"each intersection rounding");
      v*=BigInt(count)*den**BigInt(P.length-k);
      if(k%2)v=-v;
      if(k<=2)counts[0]+=v;
      if(k<=4)counts[1]+=v;
      counts[2]+=v;
    }
    test(counts[0]===l2&&counts[1]===l4&&counts[2]===actual,"summed finite expansion");
  }
}
let overlaps=0, translated=0, periods=0;
const omega=m=>P.filter(p=>m%p===0).length;
for(let d=1;d<=150;d++)for(let q=1;q<=130;q++){
  const count=omega(d)+P.filter(p=>d%p!==0&&q%p===0).length;
  test(omega(d*q)===count,"exact shared-prime correction");
  if(omega(d)+omega(q)>count)++overlaps;
}
function gcd(a,b){for(;b;)[a,b]=[b,a%b];return a;}
function lcm(a,b){return a/gcd(a,b)*b;}
function Ln(n){let l=1n;for(let d=n+1;d<2*n;d++)l=lcm(l,BigInt(d));return l;}
for(let n=8;n<=90;n++){
  const l=Ln(n),x=l+BigInt(n);
  for(const y of [8*n,9*n+1,15*n-1,Math.max(n*n,8*n)]){
    for(let m=Math.floor(3*y/4)+1;m<=y;m++){
      let witness=0;
      for(let k=Math.floor(y/(2*n))+1;4*n*k<=3*y;k++){
        if(m%k)continue;
        const d=m/k,M=l+BigInt(m);
        test(n<d&&d<2*n,"complementary divisor strict range");
        test(x<M&&M<x+BigInt(y),"translated point inside open interval");
        test(M%BigInt(d)===0n,"lcm translation keeps divisor");
        witness++;
      }
      if(witness)++translated;
    }
  }
}
// Exact arithmetic for the maximum-at-least-period-mean step.
for(let n=2;n<=6;n++){
  const l=Number(Ln(n));
  const slots=Array.from({length:l},(_,m)=>{
    for(let d=n+1;d<2*n;d++)if(m%d===0)return 1;
    return 0;
  });
  const densityN=slots.reduce((a,b)=>a+b,0);
  for(const y of [n,2*n+3,55,l+1]){
    let c=0;
    for(let h=1;h<y;h++)c+=slots[h%l];
    let sum=0,best=0;
    for(let x=0;x<l;x++){
      sum+=c;best=Math.max(best,c);
      c+=slots[(x+y)%l]-slots[(x+1)%l];
    }
    test(sum===(y-1)*densityN,"open-window periodic average");
    test(best*l>=sum,"some translate attains mean");++periods;
  }
}
test(overlaps>0&&translated>0&&periods>0&&D>0n,"nontrivial fixtures");
console.log({checks,overlaps,translated,periods});
