'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),W=849,C=33,V=307,pow=R.map(x=>R.slice(0,7).map(j=>x**j%p));
const assert=(b,e)=>{if(!b)throw Error(e);};
const H=new Uint8Array(17),types={},qset=new Set();
for(let d=2;d<=6;d++){
 const A=Array(d+1).fill(0),hist={};types[d]=hist;
 function rec(j){
  if(j<=d-2){for(let t=0;t<p;t++){A[j]=t;rec(j+1);}return;}
  H.fill(0);let S=0,q=0;
  for(let x=0;x<p;x++){
   let y=0;for(let k=1;k<=d;k++)y+=A[k]*pow[x][k];y%=p;
   H[y]++;S+=y;q+=y*(y-1)/2;
  }
  for(let c=0;c<p;c++){
   if(S<=102&&(102-S)%p===0&&(102-S)/p<=H[(p-c)%p]){
    const w=(q+136*(102-S)/p-255)/p;
    assert(Number.isInteger(w)&&w>0,"weight");
    hist[w]=(hist[w]||0)+1;
    if(d===2)qset.add([w,c].join());
   }
   const z=H[p-1-c];
   q+=S-136*z;
   S+=p-p*z;
  }
 }
 for(let a=1;a<p;a++){A[d]=a;rec(1);}
 const ww=Object.keys(hist).map(Number);
 assert(Math.min(...ww)===[8,6,4,3,2][d-2]&&Math.max(...ww)===[12,16,19,20,23][d-2],"profile extrema");
}
assert(qset.size===4&&["12,2","9,4","11,12","8,14"].every(z=>qset.has(z)),"quadratic catalog");
const q=[...qset].map(z=>z.split(",").map(Number));
for(const a of q)for(const b of q)for(const c of q)for(const d of q)
 if([a,b,c,d].reduce((s,u)=>s+u[0],0)===33)
  assert([a,b,c,d].reduce((s,u)=>s+u[1],0)%17!==1,"quadratic tight pattern");
const u=18*W-C*V;
function gap(N,hi){
 const q=17*(V-N);
 const L=C*(W*W*q+u*u*N),R=hi*V*q;
 assert(L>R,"indicator comparison");
 return (L-R)/(C*V*q);
}
const norm5=279*W+C*810,norm4=225*W+C*864;
const onlyOneSextic=Math.ceil((8*W-3*(10*20+13)-4*C)/C);
const atLeastOneQuintic=Math.ceil((7*W-2*(11*20+13)-4*C)/C);
const atLeastOneQuartic=Math.ceil((6*W-(12*19+14)-4*C)/C);
assert(onlyOneSextic===183&&atLeastOneQuintic===162&&atLeastOneQuartic===144,"support bound");
gap(onlyOneSextic,norm5);gap(atLeastOneQuintic,norm5);gap(atLeastOneQuartic,norm4);
let worst=[Infinity];
for(let t=0;t<=240;t++){
 const N=Math.ceil((8*W-3*t-4*C)/C);
 const high=329*W-50*t+C*(810+600);
 const g=gap(N,high);
 if(g<worst[0])worst=[g,t,N];
}
assert(worst[1]===240&&worst[2]===180&&5*W%C===21,"remaining arithmetic");
console.log({types,q:[...qset],onlyOneSextic,atLeastOneQuintic,atLeastOneQuartic,worst});
