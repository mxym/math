'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),mod=x=>(x%p+p)%p;
const inv=R.map(a=>R.find(b=>mod(a*b)===1));
const L=[0,1,2,3,4,5,6,7,8,9,11,15],S=new Set(L),square=new Set(R.slice(1).map(a=>mod(a*a)));
const lambda=L.map(s=>inv[L.reduce((v,t)=>s===t?v:mod(v*(s-t)),1)]);
const pow=(x,d)=>{let a=1;while(d--)a=mod(a*x);return a;};
const transforms=[];
for(const a of R)for(const b of R)for(const c of R)for(const d of R){
 if([a,b,c,d].find(x=>x)!==1||!mod(a*d-b*c))continue;
 const factor=s=>s===17?b:mod(a+b*s);
 const map=s=>factor(s)?mod((s===17?d:c+d*s)*inv[factor(s)]):17;
 if(L.every(x=>S.has(map(x))))transforms.push({factor,map});
}
const active=new Set();
let same=0,swap=0;
for(const g of transforms){
 let scale;
 for(let i=0;i<L.length;i++){
  const j=L.indexOf(g.map(L[i])),v=mod(pow(g.factor(L[i]),10)*lambda[i]*inv[lambda[j]]);
  scale??=v;
  if(scale!==v||!scale)throw Error('decic leading coefficient transformation');
 }
 if(square.has(scale))same++;else swap++;
 for(let h=0;h<=17;h++){
  const z=g.map(h);let scale;
  for(let i=0;i<L.length;i++){
   const j=L.indexOf(g.map(L[i]));
   const x=mod(lambda[i]*(h===17?1:L[i]-h)*pow(g.factor(L[i]),9));
   const y=mod(lambda[j]*(z===17?1:L[j]-z));
   if(!x!==!y)throw Error('nonic leading support transformation');
   if(x){const ratio=mod(x*inv[y]);scale??=ratio;if(ratio!==scale)throw Error('nonic leading scale');}
  }
 }
}
const orbit=h=>Array.from(new Set(transforms.map(g=>g.map(h)))).sort((a,b)=>a-b);
const a=orbit(0),b=orbit(10);
if(transforms.length!==12||same!==6||swap!==6||String(a)!==String(L)||String(b)!=='10,12,13,14,16,17')throw Error('stabilizer');
console.log({stabilizer:transforms.length,decicSame:same,decicSwap:swap,nonicOrbits:[a,b]});
