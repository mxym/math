"use strict";
// Standalone cyclotomic lattice geometry checks; generated toy inputs only.
let exact=0, floating=0;
function check(ok,msg,fp=false){
  if(!ok)throw Error(msg);
  if(fp) ++floating; else ++exact;
}
const mod=(a,n)=>(a%n+n)%n;
const primes=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67];
let state=84291387;
function rand(k){
  state=(Math.imul(state,1664525)+1013904223)>>>0;
  return state%k;
}
function boundedPower(a,b,c){
  let result=1;
  for(let j=0;j<b;++j){
    result*=a;
    if(result>c)return c+1;
  }
  return result;
}
function boxes(p,m,support){
  let k=1;
  while(boundedPower(k+1,support.length-1,p-1)<=p-1) ++k;
  check(boundedPower(k,support.length-1,p-1)<p,"fewer boxes than trial residues");
  check(boundedPower(k+1,support.length-1,p-1)>p-1,"maximal box subdivision");
  const dirs=support.slice(1).map(v=>v-support[0]), seen=new Map();
  for(let b=0;b<p;++b){
    const key=dirs.map(v=>Math.floor(mod(b*v,m)*k/m)).join(",");
    if(seen.has(key)){
      const delta=b-seen.get(key);
      check(delta>0&&delta<p&&delta%p!==0,"embedding direction is a unit");
      for(const v of dirs){
        const e=mod(delta*v,m), t=Math.min(e,m-e);
        check(t*k<m,"small phase direction as integer inequality");
      }
      return;
    }
    seen.set(key,b);
  }
  throw Error("missing pigeonhole collision");
}
for(const p of primes)
for(let a=1;a<=3;++a){
  const h=p**(a-1), m=p*h,e=(p-1)*h,d=a*e-h;
  check((2*d)%e===0?p===3:p!==3,"rational-similarity valuation");
  if(p>31&&a===3)continue;
  for(let it=0;it<96;++it){
    const c=new Map();
    const set=(v,b)=>c.set(v,(c.get(v)||0)+b);
    const ops=it%13+1;
    for(let j=0;j<ops;++j){
      const row=rand(h),k=rand(p);
      // Make the two exponents genuinely distinct.
      const ell=(k+1+rand(p-1))%p;
      const weight=rand(7)-3 || 1;
      set(row+k*h,weight);set(row+ell*h,-weight);
    }
    const terms=[...c].filter(x=>x[1]!==0), S=new Map();
    for(const [v,b] of terms)S.set(v%h,(S.get(v%h)||0)+b);
    check([...S.values()].every(b=>b===0),"centered block representatives");
    if(terms.length===0)continue;
    const E=terms.reduce((u,v)=>u+v[1]**2,0), norm=terms.reduce((u,v)=>u+Math.abs(v[1]),0);
    check(terms.length<=norm&&norm<=E&&E%2===0,"sparse energy bounds");
    let trace=0n;
    for(const [v,b] of terms)for(const [w,d] of terms){
      const k=v-w;
      const c=(k%m===0?m:0)-(k%h===0?h:0);
      trace+=BigInt(b)*BigInt(d)*BigInt(c);
    }
    check(trace===BigInt(m)*BigInt(E),"primitive-root Parseval");
    if(E===2)check(terms.length===2&&terms[0][0]%h===terms[1][0]%h,
                   "energy-two support is one root sibling");
    boxes(p,m,terms.map(x=>x[0]));
  }
  // A separate floating illustration of the exact trigonometric extremum.
  const mags=Array.from({length:p-1},(_,k)=>2*Math.sin(Math.PI*(k+1)/p));
  const x=Math.max(...mags),y=Math.min(...mags);
  check(Math.abs(x-2*Math.cos(Math.PI/(2*p)))<1e-13,"root sibling maximum",true);
  check(Math.abs(x/y-1/(2*Math.sin(Math.PI/(2*p))))<1e-11,"root sibling condition",true);
}
for(let a=2;a<=8;++a){
  const e=2**(a-1),d=(a-1)*e;
  check(2*d%e===0,"2-adic valuation");
}
console.log("Cyclotomic codifferent geometry: "+exact+" exact checks and "+floating+" floating illustrations passed.");
