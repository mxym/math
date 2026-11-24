// Node BigInt audit of actual middle/deep receiver rails and YY effect.
"use strict";
const tick=1000000n;
const loM=33390005752037n,loC=92609478893615n;
const denom=10n**15n,y=3537083851n,yDen=10n**10n;
const ok=(x,msg)=>{if(!x)throw Error(msg);};
let cells=0,m1=0n,m2=0n,m3=0n,minE=10n**10n,maxLevel=0n;
for(let vi=5;vi<170;vi++){
 const v0=BigInt(vi)*1000n,v1=v0+1000n,B=499000n+v0/2n;
 for(let ti=0;ti<105;ti++){
  const t0=ti===0?200n:BigInt(ti)*1000n,t1=BigInt(ti+1)*1000n;
  if(t1>v0)continue;
  const E=B-t1-v1,x1=tick-t0-v0;
  const z=(x1/5n>v1?x1/5n:v1)+100n;
  ok(E<4n*z,"all true old cells in linear formula range, if lower admitted");
  if(E<=2n*z)continue;
  ok(E>t1 && E+t1>400000n,"two true slot scales positive");
  // Gap delta=1 tick, theta=7/32, Proposition epsilon=.1 tick.
  const r1=2n+2n*B-v1;
  const r2=32n*(1n+2n*B+3n*v1)+7n*tick;
  const r3=16n*(1n+2n*B+3n*v1)+7n*(1n+B-v0-v1);
  ok(r1<999000n && r2<32n*1900000n && r3<16n*1935000n,"actual Prop 5.2 rails");
  cells++;
  if(r1>m1)m1=r1;if(r2>m2)m2=r2;if(r3>m3)m3=r3;
  if(E<minE)minE=E;if(B>maxLevel)maxLevel=B;
 }
}
const tot=loM+loC, lower=tot*y,base=denom*yDen;
ok(tot===125999484645652n,"prior disjoint certified amplitudes");
ok(lower*100000n>4456n*base,"true YY > .04456");
ok(lower*100000n>2n*2228n*base,"centered Y-slice < -.02228");
const show=(a,b)=>Number(a*10n**14n/b)/1e14;
console.log(JSON.stringify({candidateRailCells:cells,maxPhysicalLevel:show(maxLevel,tick),minQuotientLevel:show(minE,tick),maxRails:[show(m1,tick),show(m2,32n*tick),show(m3,16n*tick)],positiveYYLower:show(lower,base),covarianceYSliceUpper:-show(lower,2n*base)}));