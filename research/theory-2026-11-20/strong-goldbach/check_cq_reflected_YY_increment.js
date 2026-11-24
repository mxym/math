"use strict";
const Q=(n,d=1)=>{n=BigInt(n);d=BigInt(d);if(d===0n)throw Error("zero denominator");return d<0n?[-n,-d]:[n,d];};
const a=([n,d],[m,k])=>Q(n*k+m*d,d*k),s=([n,d],[m,k])=>Q(n*k-m*d,d*k);
const f=([n,d],[m,k])=>Q(n*m,d*k),div=([n,d],[m,k])=>Q(n*k,d*m);
const pow=([n,d],j)=>Q(n**BigInt(j),d**BigInt(j));
const lt=([n,d],[m,k])=>n*k<m*d,eq=(a,b)=>!lt(a,b)&&!lt(b,a);
const one=Q(1),lo=Q(4,100),hi=Q(105,1000),cut=Q(17,100);
const cn=x=>[x,Q(0)],id=[Q(0),Q(1)],b4=[Q(1,4),Q(-1,4)],b6=[Q(1,6),Q(-1,6)];
const z=([u,b],t)=>a(u,f(b,t)),p=(m,r)=>[s(one,f(Q(m),r[0])),s(Q(-1),f(Q(m),r[1]))];
function ok(test,msg){if(!test)throw Error(msg);}
for(const t of [lo,hi])ok(lt(t,z(b6,t))&&lt(z(b6,t),cut)&&lt(cut,z(b4,t)),"whole sorted integration range");
const int3=([u,b])=>b[0]===0n?f(pow(u,3),s(hi,lo)):div(s(pow(z([u,b],hi),4),pow(z([u,b],lo),4)),f(Q(4),b));
const j3=(m,l,r)=>s(int3(p(m,l)),int3(p(m,r)));
const int0=(l,r)=>div(j3(4,l,r),Q(144)),int1=(l,r)=>s(int0(l,r),div(j3(1,l,r),Q(225)));
const m1=f(Q(1920),int0(cn(cut),b4)),m2=f(Q(1920),int1(id,b6)),m=a(m1,m2);
ok(eq(m1,Q(427713,32000000))&&eq(m2,Q(109105061,900000000))&&eq(m,Q(969075913,7200000000)),"closed exact rank-five integral");
const c=Q(125999484645652n,10n**15n),y=Q(3537083851n,10000000000n),extra=f(m,c),v=f(a(m,y),c);
ok(lt(Q(1695,100000),extra)&&lt(Q(6152,100000),v),"true YY increase and replacement");
// Independent directed-rectangle enclosure, not reusing either antiderivative.
const H=20000n;let lower=0n,upper=0n;
const max0=x=>x<0n?0n:x;
for(let i=800n;i<2100n;i++){
 for(let j=3400n;i+4n*j<H;j++){
  const yup=H-i-4n*j,ydn=yup-5n;
  upper+=25n*yup*yup;
  if(ydn>=0n)lower+=25n*ydn*ydn;
 }
 for(let j=i;i+6n*j<H;j++){
  const yup=H-i-4n*j,ydn=yup-5n, xup=H-i-j,xdn=xup-2n;
  upper+=max0(25n*yup*yup-4n*xdn*xdn);
  if(j>=i+1n&&i+6n*j+7n<=H)lower+=max0(25n*ydn*ydn-4n*xup*xup);
 }
}
const ml=Q(1920n*lower,300n*H**4n),mu=Q(1920n*upper,300n*H**4n);
ok(lt(ml,m)&&lt(m,mu),"independent directed mass enclosure");
ok(lt(Q(1343,10000),ml)&&lt(mu,Q(1349,10000)),"directed interval width");
const shown=([n,d])=>Number(n*10n**16n/d)/1e16;
console.log(JSON.stringify({mCases:[m1,m2].map(shown),m:shown(m),independentMassLo:shown(ml),independentMassHi:shown(mu),bothYExtra:shown(extra),YYlower:shown(v)}));
