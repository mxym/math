'use strict';
/* Fixed-lattice geometry fixtures, rational shell replay, Gaussian numerical
 * checks. The proof is analytic; tests need only built-in assertions. */
const assert=require('node:assert/strict');
const range=n=>Array.from({length:n},(_,i)=>i);
const sum=x=>x.reduce((p,v)=>p+v,0);
const choose=(n,k)=>{
  let c=1;for(let j=1;j<=k;j++)c=c*(n-j+1)/j;return c;
};
let exact=0,numerical=0;
function ck(a,b){assert.deepEqual(a,b);exact++;}
function le(a,b,rtol=3e-12){
  assert(a<=b+rtol*Math.max(Math.abs(a),Math.abs(b),1e-250),String([a,b]));numerical++;
}
function eq(a,b){le(a,b);le(b,a);}
function lt(a,b){assert(a<b,String([a,b]));numerical++;}
function grids(n,d,visit){
  function rec(a){if(a.length===n){visit(a);return;}
    for(let j=0;j<d;j++)rec([...a,j]);}rec([]);
}
// Coordinate grid 0, 1/4, 1/2, squared distance multiplied by 16.
for(let n=1;n<=9;n++){
  let maxD=0,maxC=0,countD=0,countC=0;
  grids(n,3,ts=>{
    const a=sum(ts.map(t=>t*t)),b=sum(ts.map(t=>(2-t)**2));
    const td=Math.max(...ts),e=Math.max(a,a+16-8*td),g=Math.min(a,b);
    const geomD=(n<=4&&ts.every(t=>t===0))||(n>=4&&ts.every(t=>t===2));
    const cs=ts.filter(t=>t===1).length,zz=ts.filter(t=>t===0).length,hh=n-cs-zz;
    const geomC=cs===n%2&&zz===hh;
    ck(e===Math.max(16,4*n),geomD);
    ck(g===2*n-n%2,geomC);
    if(geomD)countD++;
    if(geomC)countC++;
    maxD=Math.max(maxD,e);maxC=Math.max(maxC,g);
  });
  ck(maxD,Math.max(16,4*n));ck(maxC,2*n-n%2);
  ck(countD,n===4?2:1);
  ck(countC,n%2 ? n*choose(n-1,(n-1)/2):choose(n,n/2));
}
// Exact coefficientwise Hadamard relation. All moments on this test use
// squared distances in integer numerator units and all points in the radius.
function shell(nums,den,R){
  const even=new Map(),all=new Map(),Rroot=Math.floor(Math.sqrt(R));
  function rec(i,Q,parity){
    if(i===nums.length){
      all.set(Q,(all.get(Q)||0)+1);
      if(parity%2===0)even.set(Q,(even.get(Q)||0)+1);
      return;
    }
    for(let m=Math.ceil((nums[i]-Rroot)/den);m<=Math.floor((nums[i]+Rroot)/den);m++){
      const v=Q+(den*m-nums[i])**2;
      if(v<=R)rec(i+1,v,parity+m);
    }
  }
  rec(0,0,0);return {even,all};
}
for(const den of [6,10,12,14]){
  const R=(3*den)**2;
  for(let t=0;t<=den/2;t++){
    const x=shell([den+t,t,t,t],den,R);
    const y=shell([den/2+2*t,den/2,den/2,den/2],den,R);
    for(let v=0;v<=R;v++){
      ck(x.even.get(v)||0,y.even.get(v)||0);
      ck(2*(y.even.get(v)||0),y.all.get(v)||0);
    }
  }
}
function PM(alpha,t){
  // All checked t are bounded; terms outside this cutoff are negligible
  // at these test alpha. No claim that this is a certified analytic bound.
  let e=0,o=0;for(let k=-16;k<=16;k++){
    const a=Math.exp(-alpha*(k-t)**2);if(k%2)o+=a;else e+=a;
  }
  return [e+o,e-o,e,o];
}
function dNorm(alpha,x){
  let even=1,odd=0;
  for(const t of x){const [,,e,o]=PM(alpha,t);[even,odd]=[even*e+odd*o,odd*e+even*o];}
  return even;
}
function cNorm(alpha,x,sides=x.map(()=>1)){
  let p=1,m=1;for(let j=0;j<x.length;j++){
    p*=PM(alpha*sides[j]**2,x[j])[0];
    m*=PM(alpha*sides[j]**2,x[j]-0.5)[0];
  }return p+m;
}
function rng(seed){return ()=>{seed=(1664525*seed+1013904223)>>>0;return seed/2**32;};}
const rand=rng(7383);
for(const alpha of [1.5,2,3.1,5,8,16,35,64]){
  const [A,,E0,O0]=PM(alpha,0),[B]=PM(alpha,0.5),[C]=PM(alpha,0.25);
  lt(2*C,A+B);
  lt(cNorm(alpha,[0,0.25,0.5]),cNorm(alpha,[0,0.5,0.5]));
  const q=Math.exp(-(Math.PI**2)/alpha),beta=[];
  for(let j=1;;j++){const p=q**(2*j-1);if(p<1e-18)break;beta.push(2*p/(1+p*p));}
  let last=-Infinity;
  for(let j=0;j<=80;j++){
    const c=j/40-1,w=beta.map(b=>b/(1-b*b*c*c));
    const v=c*sum(w.map((p,i)=>p*beta[i]))/sum(w);
    lt(last,v);last=v;
  }
  for(let j=0;j<=32;j++){
    const t=j/64;const [P,M,E,O]=PM(alpha,t);
    eq(4*E*O*(P*P+M*M),PM(alpha,0.5+2*t)[0]*B**3);
  }
  for(let n=1;n<=9;n++){
    const targetD=n<4?[1,...range(n-1).map(()=>0)]:range(n).map(()=>0.5);
    const targetC=range(n).map(i=>i<Math.floor(n/2)?0:(i===n-1&&n%2)?0.25:0.5);
    const d=n<4?sum(range(n+1).filter(j=>j%2).map(j=>choose(n,j)*E0**(n-j)*O0**j)):B**n/2;
    const c=n%2?2*C*(A*B)**((n-1)/2):2*(A*B)**(n/2);
    eq(d,dNorm(alpha,targetD));eq(c,cNorm(alpha,targetC));
    if(n===4)eq(d,dNorm(alpha,[1,0,0,0]));
    for(let trial=0;trial<35;trial++){
      const v=range(n).map(()=>2*rand()-0.5);
      le(d,dNorm(alpha,v));le(c,cNorm(alpha,v));
    }
  }
}
for(const alpha of [0.6,0.75,0.9]){
  lt(cNorm(alpha,[0.25,0],[2,1]),cNorm(alpha,[5/16,0],[2,1]));
}
console.log('PASS: '+exact+' exact checks and '+numerical+' numerical checks');
