// Run: node verify_factor_odd_covering_valuation.js
// All inequalities are checked with outward-rounded nonnegative integer arithmetic.
"use strict";
function verify() {
  const W=10n**30n, B0=30000, B1=1000000, H=9900;
  let checks=0;
  const ok=(x,m)=>{++checks;if(!x)throw Error(m);};
  const up=(n,d)=>{if(n<0n||d<=0n)throw Error("rounding domain");return (n+d-1n)/d;};
  const sw=new Uint8Array(B1+1), pp=[];
  for (let p=2;p<=B1;p++) if(!sw[p]) {
    pp.push(p); if(p*p<=B1) for(let k=p*p;k<=B1;k+=p)sw[k]=1;
  }
  ok(pp.length===78498,"prime count through 1000000");
  const b=BigInt(pp.length-1);
  ok(11n**11n<b*4n**11n,"log b > 11 via e < 11/4");
  ok((27n-13n)**2n>156n,"moment tail inequality for p >= 27");
  function pure(p,cap) {
    if(cap===Infinity)return [p-1n,p-2n,1n,p-1n];
    const pk=p**BigInt(cap), wn=pk-1n, wd=pk*(p-1n);
    return [wd,wd-wn,wn,wd];
  }
  function moment(p,cap,g,r){
    if(cap===Infinity) {
      const v=p-1n;
      const [u,d]=r===1?[1n,v]:[7n*p*p-2n*p+1n,v**3n];
      return [g[1]*d+g[0]*u,g[1]*d];
    }
    const dn=g[1]*p**BigInt(cap);
    let n=dn;
    for(let k=1;k<=cap;k++)n+=g[0]*(BigInt(k+1)**BigInt(r)-BigInt(k)**BigInt(r))*p**BigInt(cap-k);
    return [n,dn];
  }
  const probs=(p,cap,g)=>{
    const h=Math.min(10,cap+1), a=[[g[1]*p-g[0],g[1]*p]];
    for(let d=2;d<=h;d++){
      a.push(d===h?[g[0],g[1]*p**BigInt(d-1)]:[g[0]*(p-1n),g[1]*p**BigInt(d)]);
    }
    return a;
  };
  const xyz=[];
  for(let t=1;t<=H;t++){
    let u=t;for(const q of [2,3,5,7])while(u%q===0)u/=q;
    if(u===1)xyz.push(t);
  }
  const shape=(mode,p)=>{
    if(mode==="E"){if(p===13||p===19)return [1n,3n];if(p===17)return [1n,4n];}
    // For D only, modestly increase the threshold at the early ordinary primes.
    if(mode==="D"&&p<61)return [33n,100n];
    if(p>B0)return [1n,2n];
    return [3n,10n];
  };
  const ceilMoment=(m,r)=>up(m*r[0],r[1]);
  const cases=[
    [7,2,Infinity,"A"],[7,Infinity,1,"B"],[11,2,1,"C"],[13,2,1,"D"],[7,3,2,"E"]
  ];
  function compute([miss,a3,a5,name]) {
    const g3=pure(3n,a3), g5=pure(5n,a5);
    let M1=ceilMoment(W,moment(3n,a3,g3,1)), M3=ceilMoment(W,moment(3n,a3,g3,3));
    const probs3=probs(3n,a3,g3), probs5=probs(5n,a5,g5);
    let dp=Array(H+1).fill(0n);
    for(let d=1;d<=probs3.length;d++)dp[d]=ceilMoment(W,probs3[d-1]);
    function dist(P) {
      const next=Array(H+1).fill(0n);
      for(let d=1;d<=P.length;d++){
        const [a,z]=P[d-1];
        for(const t of xyz){
          const u=t*d;if(u>H)break;
          if(dp[t]!==0n)next[u]+=up(dp[t]*a,z);
        }
      }
      dp=next;
    }
    // The only remaining 5-stage classes have both 3 and 5 in their modulus.
    const stage5=up((M1-W)*g5[0]*g5[2],g5[1]*g5[3]);
    dist(probs5);
    M1=ceilMoment(M1,moment(5n,a5,g5,1));M3=ceilMoment(M3,moment(5n,a5,g5,3));
    let S=stage5, mid=0n;
    for(const q of pp) {
      if(q<7||q===miss)continue;
      const p=BigInt(q), v=p-1n, [z,d]=shape(name,q), gamma=[d,d-z];
      if(q<=B0){
        const a=z*v;
        ok(2n*z<=d&&a<=d*BigInt(H),"distortion and state range");
        let sum=d*M1-a*W;
        for(const t of xyz){
          const coeff=a-d*BigInt(t);if(coeff<=0n)break;
          sum+=coeff*dp[t];
        }
        S+=up(sum,(d-z)*v);
        dist(probs(p,Infinity,gamma));
        M1=ceilMoment(M1,moment(p,Infinity,gamma,1));
      } else {
        ok(2n*z===d,"tail distortion");
        mid+=up(32n*M3,27n*v**3n);
      }
      M3=ceilMoment(M3,moment(p,Infinity,gamma,3));
    }
    const tail=up(32n*M3,27n*b*b*1210n);
    const total=S+mid+tail;
    ok(total<W,"not enough margin in "+name);
    const upperPPM=n=>Number(up(n*1000000n,W));
    return {name, missingPrime:miss, maxV3:String(a3),maxV5:String(a5),
            finitePPM:upperPPM(S),middlePPM:upperPPM(mid),tailPPM:upperPPM(tail),totalPPM:upperPPM(total)};
  }
  const rows=cases.map(compute);
  return {checks,rows};
}
console.log(JSON.stringify(verify(),null,2));
