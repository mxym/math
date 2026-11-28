import { readFileSync } from "node:fs";
// Exact finite support and mandatory-modulus replay for the odd-covering problem.
// Run with Node, no dependencies.
function oddRational(){
 const abs=x=>x<0n?-x:x;
 function Q(n,d=1n){
  n=BigInt(n);d=BigInt(d);
  if(d===0n)throw Error("zero denominator");
  if(d<0n){n=-n;d=-d;}
  let a=abs(n),b=d;
  while(b){[a,b]=[b,a%b];}
  if(!a)return [0n,1n];
  return [n/a,d/a];
 }
 const add=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
 const sub=(a,b)=>add(a,[-b[0],b[1]]);
 const mul=(a,b)=>Q(a[0]*b[0],a[1]*b[1]);
 const inv=a=>Q(a[1],a[0]);
 const Z=Q(0),O=Q(1);
 function evalLoss(primes,caps,schedule,omit=null){
  const r=primes.length;
  const at=omit?omit.reduce((i,x,j)=>x?j:i,-1):-1;
  const pure=omit&&omit.filter(x=>x).length===1;
  const eta=[1,1,...schedule.map(x=>x[0])];
  const delta=[Z,Z,...schedule.map(x=>Q(x[1],10000))];
  const power=primes.map((p,i)=>BigInt(p)**BigInt(caps[i]));
  const s=primes.map((p,i)=>Q(power[i]-1n,BigInt(p-1)*power[i]));
  const removed=at<0?Z:Q(1n,BigInt(primes[at])**BigInt(omit[at]));
  const g=s.map((x,i)=>eta[i]?inv(sub(add(O,pure&&at===i?removed:Z),x)):O);
  const u=s.map((x,i)=>mul(x,g[i]));
  const c=delta.map(x=>inv(sub(O,x)));
  let all=new Map([[1,1n]]), relevant=new Map([[1,1n]]), den=1n, total=Z;
  function accumulate(m,f){
   for(const [k,v] of m)f(k,v);
  }
  for(let i=0;i<r;i++){
   const P=u[i][0]*delta[i][1], Qd=delta[i][0]*u[i][1];
   const denom=u[i][1]*delta[i][1];
   let stage=0n;
   accumulate(all,(k,val)=>{
    const y=P*BigInt(k-eta[i])-Qd;
    if(y>0n)stage+=val*y;
   });
   let stageLoss=Q(stage,denom*den);
   if(at===i&&!(pure&&eta[i])){
    const amount=mul(removed,g[i]);
    let lost=0n;
    accumulate(relevant,(k,val)=>{
     const y=(P*BigInt(k-eta[i])-Qd)*amount[1];
     if(y<=0n)return;
     const d=denom*amount[0];
     lost+=val*(y<d?y:d);
    });
    stageLoss=sub(stageLoss,Q(lost,denom*amount[1]*den));
   }
   total=add(total,mul(c[i],stageLoss));
   if(i+1===r)break;
   const gamma=mul(c[i],g[i]);
   const scale=gamma[1]*power[i];
   const tails=[scale];
   for(let e=1,p=BigInt(primes[i]);e<=caps[i];e++,p*=BigInt(primes[i]))tails.push(gamma[0]*power[i]/p);
   tails.push(0n);
   if(tails.some((x,j)=>j>0&&x>tails[j-1]))throw Error("invalid tail");
   function evolve(current,required){
    const z=new Map();
    accumulate(current,(x,y)=>{
     for(let j=required;j<tails.length-1;j++){
      const k=x*(j+1), w=(tails[j]-tails[j+1])*y;
      if(w)z.set(k,(z.get(k)??0n)+w);
     }
    });
    return z;
   }
   all=evolve(all,0);
   if(at>i)relevant=evolve(relevant,omit[i]);else relevant=new Map();
   den*=scale;
  }
  return total;
 }
 const exact=(a,b)=>a[0]*b[1]<b[0]*a[1];
 const ppm=q=>Number((q[0]*1000000n+q[1]-1n)/q[1]);
 return {Q,evalLoss,exact,ppm};
}
const arithmetic=oddRational();
const PRIMES=[3,5,7,11,13,17,19,23,29,31,37,41,43];
const LIMIT=473824157932125n;
const counts=[1081,211,20,1];
const ceilings=[998264,993646,843424,561855];
const reports=[];
const require=(ok,why)=>{if(!ok)throw Error(why);};
const product=(p,a)=>p.reduce((q,x,i)=>q*BigInt(x)**BigInt(a[i]),1n);
const known=(r,x=1700)=>[[1,x],[1,3000],[1,4150],[0,4700],[1,3900],...Array.from({length:r-7},()=>[1,5000])];
const rounded=(p,a,s,omit=null)=>arithmetic.ppm(arithmetic.evalLoss(p,a,s,omit));
if(process.argv.length!==3)throw Error("Usage: node verifier.mjs schedule.json");
const necessary=JSON.parse(readFileSync(process.argv[2],"utf8"));
function cases(primes){
 const start=primes.reduce((a,p)=>a*BigInt(p),3n);
 const ans=[];
 function visit(i,b,cap){
  if(i===primes.length){ans.push(cap);return;}
  const p=BigInt(primes[i]);let e=i===0?2:1;
  for(let x=b;x>=1n;x/=p)visit(i+1,x,[...cap,e++]);
 }
 visit(0,(LIMIT-1n)/start,[]);
 return ans;
}
for(let r=9;r<=12;r++){
 const ps=PRIMES.slice(0,r),caps=cases(ps),bad=[];
 let max=0;
 for(const a of caps){
  const v=Math.min(rounded(ps,a,known(r)),rounded(ps,a,known(r,1950)));
  if(v>=1000000)bad.push(a.join(","));
  else max=Math.max(max,v);
 }
 require(caps.length===counts[r-9]&&max===ceilings[r-9],"rank census mismatch");
 const expected=r===9?necessary.map(x=>x.a.join(",")):[];
 require(JSON.stringify(bad)===JSON.stringify(expected),"wrong exceptional profiles");
 reports.push({r,profiles:caps.length,ceilingPPM:max,exceptions:bad});
}
require(PRIMES.reduce((a,p)=>a*BigInt(p),3n)>=LIMIT,"rank-13 baseline too low");
const shift=[3,5,7,11,13,17,19,23,31];
const t=[[0,3265],[0,3967],[0,4615],[0,4706],[0,4211],[1,5000],[1,5000]];
const shifted=necessary.map(({a})=>Math.min(...[known(9),known(9,1950),t].map(s=>rounded(shift,a,s))));
require(shifted.every(v=>v<1000000),"exceptional profile has a larger support");
const required=necessary.map(({a,p,forced})=>{
 const seen=new Set();let max=0;
 for(const {modulus,exp,ppm,schedule} of forced){
  require(exp.every((x,i)=>Number.isInteger(x)&&x>=0&&x<=a[i]),"omitted modulus outside cap");
  require(product(p,exp)===BigInt(modulus)&&modulus>1&&!seen.has(modulus),"invalid mandatory-modulus row");
  seen.add(modulus);
  const v=rounded(p,a,schedule,exp);
  require(v===ppm&&v<1000000,"omission failed to prove noncoverage");
  max=Math.max(max,v);
 }
 return {lcm:String(product(p,a)),forced:seen.size,maxPPM:max};
});
require(required[0].forced===70&&required[1].forced===131,"wrong mandatory count");
console.log(JSON.stringify({reports,shifted,required},null,2));
