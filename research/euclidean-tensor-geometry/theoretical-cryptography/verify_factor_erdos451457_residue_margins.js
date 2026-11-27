"use strict";

// Fixed toy configurations. All pointwise and moment comparisons are exact.
let checks=0;
function check(b,msg){ if(!b) throw new Error(msg); ++checks; }
const pop=x=>{let s=0;for(;x;x&=x-1)s++;return s;};
const bit=(x,i)=>((x>>i)&1)!==0;
const submasks=x=>{ const a=[]; for(let t=x;;t=(t-1)&x){a.push(t);if(!t)break;}return a; };
const prod=arr=>arr.reduce((a,b)=>a*BigInt(b),1n);
const abs=x=>x<0n?-x:x;
const sign=mask=>pop(mask)%2?-1n:1n;

for(const {k,near,far} of [
  {k:3,near:[5],far:[7]},
  {k:6,near:[7,11],far:[13]},
  {k:10,near:[11,13,17,19],far:[23]},
  {k:14,near:[17,19,23],far:[29,31]},
  {k:22,near:[23,29,31,37,41,43],far:[47,53]}
]){
  const m=near.length, P=near.concat(far), M=1<<P.length, MA=1<<m, all=M-1;
  const Q=prod(P), QA=prod(near);
  const mass=Array.from({length:M},(_,x)=>prod(P.map((p,i)=>bit(x,i)?p-k:k)));
  const massA=mass.slice(0,MA).map(z=>z/(BigInt(k)**BigInt(far.length)));
  check(mass.reduce((a,b)=>a+b,0n)===Q,"product weights");
  const start=3000+37*k, N=1021+19*k;
  const counts=Array(M).fill(0n);
  for(let n=start;n<start+N;n++){
    const miss=P.reduce((mask,p,i)=>{
      // An independent direct check, not using the interval's modular shortcut.
      let seen=false;
      for(let j=1;j<=k;j++) if((n+j)%p===0) seen=true;
      return seen?mask:(mask|(1<<i));
    },0);
    for(const s of submasks(miss)) ++counts[s];
  }
  for(let s=0;s<M;s++){
    const den=prod(P.filter((_,i)=>bit(s,i)));
    const num=prod(P.filter((_,i)=>bit(s,i)).map(p=>p-k));
    check(abs(counts[s]*den-BigInt(N)*num)<=num*den,"arithmetical CRT error");
  }
  for(let d=0;d<=m;d++){
    const kd=BigInt(k)**BigInt(d);
    const K=Array.from({length:MA},(_,x)=>x).filter(x=>pop(x)<=d)
      .reduce((a,x)=>a+BigInt(k)**BigInt(d-pop(x))*prod(near.filter((_,i)=>bit(x,i)).map(p=>p-k)),0n);
    check(K>0n,"positive kernel normalization");
    let second=0n, countBelow=0n;
    for(let x=0;x<MA;x++){
      let val=0n;
      for(let s=0;s<MA;s++) if(pop(s)<=d) {
        const factors=near.filter((_,i)=>bit(s,i)).map(p=>bit(x,near.indexOf(p))?-k:p-k);
        val+=BigInt(k)**BigInt(d-pop(s))*prod(factors);
      }
      if(x===0) check(val===K,"kernel evaluates to one");
      second+=massA[x]*val*val;
      if(pop(x)<=d) countBelow+=massA[x];
      const lower=BigInt(1-pop(x))*val*val, upper=val*val, indicator=x===0?K*K:0n;
      check(lower<=indicator && indicator<=upper,"two sided polynomial signs");
    }
    check(second===QA*kd*K,"quadratic diagonalization");
    check(countBelow*kd===K*massA[0],"kernel-to-probability identity");
  }
  const minEven=mass.reduce((z,w,x)=>pop(x)%2?z:(w<z?w:z),mass[0]);
  const minOdd=mass.reduce((z,w,x)=>pop(x)%2?(w<z?w:z):z,mass[1]);
  for(const c of [-minEven,minOdd]) {
    const changed=mass.map((w,x)=>w+c*sign(x));
    check(changed.every(w=>w>=0n),"feasible parity endpoint");
    for(let projection=0;projection<all;projection++){
      for(const u of submasks(projection)) {
        let old=0n, now=0n;
        for(const v of submasks(all^projection)){
          old+=mass[u|v]; now+=changed[u|v];
        }
        check(old===now,"all proper binary marginals");
      }
    }
  }
}
for(const {k,P} of [{k:6,P:[7,11]},{k:10,P:[11,13,17,19]}]){
  const m=P.length, all=(1<<m)-1, Q=Number(prod(P));
  const lift=prod(P.map(p=>(p-k)*k));
  const joint=Array.from({length:all},()=>new Map());
  const D=prod(P.map(p=>p-k)); // product-model numerator of all allowed
  let total=0n;
  for(let code=0;code<Q;code++){
    let index=code, step=1, fail=0, fullSize=1n;
    const digits=[];
    for(let i=0;i<m;i++){
      const p=P[i], a=index%p;
      digits.push(a); index=Math.floor(index/p);
      if(a>=1&&a<=k){fail|=1<<i;fullSize*=BigInt(k);}
      else fullSize*=BigInt(p-k);
      step*=p;
    }
    check(step===Q && lift%fullSize===0n,"integer normalized lift");
    const mass=(fullSize-D*sign(fail))*(lift/fullSize);
    check(mass>=0n && (fail!==0||mass===0n),"full allowed cell eliminated");
    total+=mass;
    for(let s=0;s<all;s++){
      let key=0, base=1;
      for(let i=0;i<m;i++)if(bit(s,i)){key+=digits[i]*base;base*=P[i];}
      joint[s].set(key,(joint[s].get(key)||0n)+mass);
    }
  }
  check(total===BigInt(Q)*lift,"full lifted mass");
  for(let s=0;s<all;s++){
    const d=prod(P.filter((_,i)=>bit(s,i)));
    check(joint[s].size===Number(d),"all projected residue tuples appear");
    for(const n of joint[s].values())check(n*d===total,"full proper residue independence");
  }
}
console.log(JSON.stringify({binaryConfigurations:5,fullResidueConfigurations:2,checks}));
