'use strict';
// Tiny exact coefficient enumerations and deterministic asymptotic-function illustration.
let checks=0;
function yes(x){checks++;if(!x)throw Error('check failed');}
function each(l,h,n,f){function rec(a){if(a.length===n){f(a);return;}for(let k=l;k<=h;k++)rec([...a,k]);}rec([]);}
for(const p of [3,5,7]){
 const root=Array(9).fill(0),dual=new Map();
 each(-2,2,p,a=>{
  const s=a.reduce((x,y)=>x+y,0),e=a.reduce((x,y)=>x+y*y,0);
  if(s===0&&e<=8)root[e]++;
  if(2*s>=-p&&2*s<p){const scaled=p*e-s*s;dual.set(scaled,(dual.get(scaled)||0)+1);}
 });
 yes(root[0]===1);
 yes(root[2]===p*(p-1));
 yes(root.filter((_,i)=>i%2).every(x=>x===0));
 yes(dual.get(0)===1);
 yes(dual.get(p-1)===2*p);
 yes([...dual.keys()].every(x=>x===0||x>=p-1));
 // Independently build the constant coefficient of the p-factor theta product.
 let poly=new Map([['0,0',1]]);
 for(let i=0;i<p;i++){
  let next=new Map();
  for(const [k,v] of poly){
   const [s,e]=k.split(',').map(Number);
   for(let j=-2;j<=2;j++)if(e+j*j<=8){
    const key=[s+j,e+j*j].join();next.set(key,(next.get(key)||0)+v);
   }
  }
  poly=next;
 }
 for(let e=0;e<=8;e++)yes(root[e]===(poly.get('0,'+e)||0));
}
function I0(x){let s=1,t=1;for(let k=1;k<=50;k++){t*=x*x/(4*k*k);s+=t;}return s;}
function midpoint(f,b,n=5000){let ans=0;for(let i=0;i<n;i++)ans+=f((i+.5)*b/n);return ans*b/n;}
const profiles=[];
for(const tau of [.02,.25,1,3]){
 const root=2/Math.sqrt(2*Math.PI)*midpoint(x=>Math.exp(-x*x/2),Math.sqrt(tau/2));
 const dual=midpoint(t=>Math.exp(-t)*Math.max(1-Math.exp(-tau)*I0(2*Math.sqrt(tau*t)),0),20);
 yes(dual>0&&dual<root);
 profiles.push({tau,root,dual});
}
console.log({exactChecks:checks-profiles.length,illustrativeProfiles:profiles});
