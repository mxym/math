// node check_cq_external_rank5_Y_block-20261124.js
"use strict";
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a;}
function Q(a,b=1n){
 a=BigInt(a);b=BigInt(b);
 if(b===0n)throw Error("zero denominator");
 if(b<0n){a=-a;b=-b;}
 const g=gcd(a,b);return [a/g,b/g];
}
const plus=([a,b],[c,d])=>Q(a*d+b*c,b*d);
const dif=([a,b],[c,d])=>Q(a*d-b*c,b*d);
const mul=([a,b],[c,d])=>Q(a*c,b*d);
const div=([a,b],[c,d])=>Q(a*d,b*c);
const pow=([a,b],k)=>Q(a**BigInt(k),b**BigInt(k));
const lt=([a,b],[c,d])=>a*d<c*b;
const eq=(a,b)=>!lt(a,b)&&!lt(b,a);
const shown=([a,b])=>Number(a*10n**16n/b)/1e16;
const ok=(p,message)=>{if(!p)throw Error(message);};
const constant=x=>[x,Q(0)],id=[Q(0),Q(1)];
const beta=Q(1,5000),d=Q(1,200),T=Q(1,25),h=Q(17,100);
const f4=[Q(1,4),Q(-1,4)],f6=[Q(1,6),Q(-1,6)];
const affine=([a,b],t)=>plus(a,mul(b,t));
ok(lt(beta,d)&&lt(d,T)&&lt(T,h),"sorted fixed endpoints");
for(const t of [beta,T]){
 ok(lt(h,affine(f4,t)),"high v cap");
 ok(lt(t,affine(f6,t))&&lt(d,affine(f6,t))&&lt(affine(f6,t),h),"third-arm cut inside bank");
}
function integralCube([a,b],lo,hi){
 const F=t=>pow(affine([a,b],t),4);
 return b[0]===0n?mul(pow(a,3),dif(hi,lo)):div(dif(F(hi),F(lo)),mul(Q(4),b));
}
const op=(j,term)=>[dif(Q(1),mul(Q(j),term[0])),dif(Q(-1),mul(Q(j),term[1]))];
const moment=(j,a,b,l,u)=>dif(integralCube(op(j,a),l,u),integralCube(op(j,b),l,u));
const I=(a,b,l,u)=>div(moment(4,a,b,l,u),Q(144));
const J=(a,b,l,u)=>dif(I(a,b,l,u),div(moment(1,a,b,l,u),Q(225)));
const m1=mul(Q(1920),I(id,constant(d),beta,d));
const m2=mul(Q(1920),I(constant(h),f4,beta,T));
const m3=mul(Q(1920),plus(J(constant(d),f6,beta,d),J(id,f6,d,T)));
const m=plus(plus(m1,m2),m3);
const cY=Q(125999484645652n,10n**15n);
const each=mul(cY,m),both=mul(Q(2),each);
ok(eq(m1,Q(218129409,122070312500)),"tiny second");
ok(eq(m2,Q(2695631353601,187500000000000)),"large second");
ok(eq(m3,Q(448484456889719n,1757812500000000n)),"third rejection");
ok(eq(m,Q(3815176514554627n,14062500000000000n)),"exact ordinary D");
ok(lt(Q(3418,100000),each)&&lt(Q(6836,100000),both),"both real directed lower");
const old=Q(378,10000),yy=Q(4456,100000),floor=Q(6836,100000);
const combined=plus(plus(old,yy),floor);
ok(eq(combined,Q(15072,100000)),"disjoint reserve sum, before signed exterior");
console.log(JSON.stringify({massCases:[m1,m2,m3].map(shown),mass:shown(m),each:shown(each),both:shown(both),combinedConservative:shown(combined)}));