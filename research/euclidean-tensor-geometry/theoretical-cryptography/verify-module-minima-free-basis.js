"use strict";
// Exact small checks of the module-basis obstruction in Q(sqrt(-5))
// and the elementary ideal-class witness in Q(sqrt(-23)).
const add=([a,b],[c,d])=>[a+c,b+d];
const neg=([a,b])=>[-a,-b];
const scale=(c,[a,b])=>[c*a,c*b];
const mult=([a,b],[c,d])=>[a*c-5*b*d,a*d+b*c];
const div2=([a,b])=>{if((a%2)||(b%2))throw Error("nonintegral division");return [a/2,b/2];};
const det=([a,b],[c,d])=>a*d-b*c;
const E=([a,b])=>2*(a*a+5*b*b);
const gcd=(a,b)=>b===0?Math.abs(a):gcd(b,a%b);
const zero=([a,b])=>a===0&&b===0;
let checks=0;
function eq(a,b,label){checks++;if(a!==b)throw Error(label+": "+a+" !== "+b);}
const I=[];
for(let a=-9;a<=9;a++)for(let b=-9;b<=9;b++)if((a-b)%2===0)I.push([a,b]);
const primitive=(x,y)=>{
  // y stores 2*yActual, so products xJ+yActual I have these integral generators.
  const gens=[x,div2(mult(x,[1,1])),y,div2(mult(y,[1,1]))];
  let g=0;
  for(let i=0;i<gens.length;i++)for(let j=0;j<i;j++)g=gcd(g,det(gens[i],gens[j]));
  return g===1;
};
const columns=[];
for(const x of I)for(const y of I)if(!zero(x)||!zero(y))
  columns.push({x,y,ex:E(x),ey:E(y)/4,prim:primitive(x,y)});
eq(Math.min(...I.filter(x=>!zero(x)).map(E)),8,"ideal minimum");
eq(Math.min(...I.filter(x=>!zero(x)).map(x=>E(x)/4)),2,"inverse ideal minimum");
eq(columns.filter(v=>v.prim && (zero(v.x)||zero(v.y))).length,0,"no pure-axis primitive");
function Bdet(v,w) {return add(mult(v.x,w.y),neg(mult(w.x,v.y)));}// twice determinant
const v={x:[1,-1],y:[2,0]},w={x:[2,0],y:[1,1]};
eq(Bdet(v,w).join(","),"2,0","determinant-one witness");
eq(primitive(v.x,v.y),true,"first column primitive");
eq(primitive(w.x,w.y),true,"second column primitive");
for(const T of [4,5,6,7,8,9,16,25,32,40]){
  // Multiply squared canonical lengths by tau^2, putting T=tau^4.
  const len=u=>u.ex+T*u.ey;
  const live=columns.filter(u=>len(u)<=3*T+8).sort((a,b)=>len(a)-len(b));
  // Bound 3*T+8 <=128 makes coefficient enumeration exhaustive here.
  eq(live[0].ex+T*live[0].ey,8,"first independent minimum");
  eq(len(live.find(x=>x.prim)),2*T+12,"primitive minimum");
  let ind=Infinity,basis=Infinity;
  for(let i=1;i<live.length;i++){
    for(let j=0;j<i;j++){
      const d=Bdet(live[i],live[j]),l=len(live[i]);
      if(!zero(d))ind=Math.min(ind,l);
      if(d[1]===0 && Math.abs(d[0])===2)basis=Math.min(basis,l);
    }
  }
  eq(ind,2*T,"second independent minimum");
  eq(basis,3*T+8,"minimum maximum basis-column length");
}
// Norm and split-prime valuations for theta^2-theta+6=0.
const normF=([a,b])=>a*a+a*b+6*b*b;
eq(normF([-2,1]),8,"theta-2 norm");
eq((-2)%2,0,"theta-2 at theta=0");
eq(Math.abs((-2+1)%2),1,"theta-2 at theta=1");
const normTwo=[];
for(let a=-2;a<=2;a++)for(let b=-2;b<=2;b++)if(normF([a,b])===2)normTwo.push([a,b]);
eq(normTwo.length,0,"norm-two impossible");
eq(gcd(11,3),1,"extension ratio");
console.log("OK: "+checks+" exact norm, determinant and minimum checks.");
