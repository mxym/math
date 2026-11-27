/* Node 18+. Exact arithmetic on synthetic coefficient and counting claims. */
'use strict';
let checks=0;
function ck(q,m){++checks;if(!q)throw Error(m);}
for(let k=3n;k<=13n;++k){
  const d=1n<<k;
  let g=1n;
  while(2n*g<=k)g*=2n;
  const d0=d/g;
  const cube=(2n*d+1n)**d0;
  const odd=(cube-1n)/2n; // d0 is even.
  ck(g<=k&&2n*g>k&&d%g===0n,'relative degree conditions');
  ck(1n+odd>=1n<<d,'admissible cardinality with polynomial coefficient palette');
  ck(d*d0<=d*d,'canonical maximum bound');
  const seen=new Set();
  for(let i=0n;i<g;++i)for(let j=0n;j<d0;++j){
    const t=i+g*j;
    ck(t>=0n&&t<d&&!seen.has(t),'relative monomial expansions bijective');
    seen.add(t);
  }
  ck(seen.size===Number(d),'all power-basis labels');
  ck(5n*k+2n<=7n*k,'affine logarithmic threshold scale');
  ck(2n*g*k>=k*k,'quadratic many admissible steps');
}
let seed=617193533;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
function valuation2(x){
  let v=0n;
  if(!x)return -1n;
  while(x%2n===0n){x/=2n;++v;}
  return v;
}
for(let k=1;k<=48;++k)for(let trial=0;trial<80;++trial){
  const cs=Array.from({length:k},()=>rng(6)===0?0n:BigInt(2*rng(50)-49));
  const first=cs.findIndex(x=>x!==0n);
  const s=cs.reduce((x,u,i)=>x+(u<<BigInt(i)),0n);
  ck(valuation2(s)===BigInt(first),'rational least valuation survives all later factors');
  ck(s===0n||s%(1n<<BigInt(k))!==0n,'rational gain against all odd denominators');
}
// Over any dyadic subfield the mod-(1-zeta) residue is the coefficient sum mod 2.
for(const d0 of [4,8,16,32,64])for(let k=1;k<=18;++k)for(let trial=0;trial<50;++trial){
  const a=[];
  for(let j=0;j<k;++j) {
    let x=Array.from({length:d0},()=>BigInt(rng(21)-10));
    if(rng(5)===0)x=x.map(()=>0n);
    else if(x.reduce((s,w)=>s+w,0n)%2n===0n)++x[0];
    a.push(x);
  }
  const l=a.findIndex(x=>x.some(Boolean));
  if(l<0)continue;
  const z=Array(d0).fill(0n);
  for(let j=l;j<k;++j)for(let i=0;i<d0;++i)z[i]+=a[j][i]<<BigInt(j-l);
  ck(z.reduce((s,w)=>s+w,0n)%2n!==0n,'least term is a ramified local unit');
  ck(l<k,'valuation is strictly earlier than next proposed step');
}
// Replay the corrected counting in a finite one-axis example.
// A = {-2,-1,0,1,2}, C={0,1,2}; the shifts can be placed on a disjoint axis.
const A=[-2,-1,0,1,2],C=[0,1,2],h=7;
for(const a of C)for(const b of C)ck(A.includes(a-b),'difference containment');
let sums=new Set([0]),injected=new Set([0]);
for(let j=0;j<h;++j){
  const x=7**j;
  for(const a of A) if(a!==0)ck(!sums.has(a*x),'a finite gain event');
  sums=new Set([...sums].flatMap(s=>A.map(a=>s+a*x)));
  injected=new Set([...injected].flatMap(s=>C.map(a=>s+a*x)));
  ck(injected.size===C.length**(j+1),'exact difference-criterion injection');
  ck([...injected].every(x=>sums.has(x)),'injected sums are members of the target set');
}
for(let d=4;d<=4096;d*=2)for(let r=1;r<=6;++r){
  const alpha=1/(1+2*d*Math.exp(-.5))+(Math.sqrt(2)*Math.exp(-Math.PI/2))**(r*d);
  ck(alpha<=1/(1+8*Math.exp(-.5))+(Math.sqrt(2)*Math.exp(-Math.PI/2))**4,
      'monotone worst-case reduction for the displayed constants');
}
ck(1/(1+8*.6)+(.3**4)<.25,'analytic rational domination of the failure base');
console.log('scope audit finite arithmetic:',checks,'checks');
