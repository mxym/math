// Node exact arithmetic for CQ compact covariance and high reference.
"use strict";
const scale=10n**14n,p=4000n,P=Number(p),p5=p**5n;
const up=(n,d)=>(n+d-1n)/d,pos=x=>x<0n?0n:x;
const psi=Array.from({length:P+1},(_,i)=>{const z=p-2n*BigInt(i);return 2n*z**3n*p**2n-z**5n;});
function ok(x,s){if(!x)throw Error(s);}
let lo2=0n,lo3=0n,hi2=0n,hi3=0n;
for(let i=624;i<2000;i++){
 lo2+=p*scale*pos(p5-psi[i])/(p5*BigInt((i+1)*(P-i)));
 hi2+=up(p*scale*pos(p5-psi[i+1]),p5*BigInt(i*(P-i-1)));
}
for(let i=624;i<=Math.floor(P/3);i++){
 for(let j=i+1;j<=Math.floor((P-i-3)/2);j++){
  const w=P-i-j;
  lo3+=p*scale*pos(p5-psi[i]-psi[j]-psi[w-2])/(p5*BigInt((i+1)*(j+1)*w));
 }
 for(let j=i;j<=Math.floor((P-i)/2);j++){
  const w=P-i-j;
  hi3+=up(p*scale*pos(p5-psi[i+1]-psi[j+1]-psi[w]),p5*BigInt(i*j*(w-2)));
 }
}
const frac=(a,b=1n)=>[BigInt(a),BigInt(b)];
const add=([a,b],[c,d])=>[a*d+b*c,b*d];
const sub=([a,b],[c,d])=>[a*d-b*c,b*d];
const mul=([a,b],[c,d])=>[a*c,b*d];
const div=([a,b],[c,d])=>[a*d,b*c];
const lt=([a,b],[c,d])=>a*d<c*b;
const show=([a,b])=>Number(a*10n**14n/b)/1e14;
const lowA=frac(1819,1000),highA=frac(1827,1000);
ok(lt(lowA,frac(lo2+lo3,scale)) && lt(frac(hi2+hi3,scale),highA),"high true A mass");
const eta=frac(372,100000000),linearLo=frac(5614584359419n,10000000000000n),linearHi=frac(5614605206538n,10000000000000n);
ok(lt(div(sub(linearHi,linearLo),linearLo),eta),"normalized width of real R-.04 comparison");
const y=frac(3537083851n,10000000000n),wabs=frac(6388,1000000),g5=frac(2n*475n**4n,3n*1000n**4n);
const b=add(add(frac(1),wabs),add(g5,div(y,frac(2))));
const by=mul(b,y),needed=sub(mul(sub(frac(1),eta),by),frac(189,10000));
const refgap=sub(mul(sub(frac(2),div(frac(131,100),lowA)),y),frac(189,10000));
ok(lt(frac(43052675553n,100000000000n),by),"ordinary paired debit baseline");
ok(lt(frac(41162515,100000000),needed),"compact gate .41162515");
ok(lt(frac(86105,100000),mul(frac(2),by)),"independent-dyadic magnitude of exact Y ledger");
ok(lt(frac(43378,100000),refgap),"high-axis backed sufficient bridge .43378");
console.log(JSON.stringify({aLo:show(frac(lo2+lo3,scale)),aHi:show(frac(hi2+hi3,scale)),byLo:show(by),gateLo:show(needed),highReferenceRhsLo:show(refgap)}));