"use strict";
// Fixed finite arithmetic checks for the proof's bookkeeping; they do not
// test the analytic rectangle estimate or probabilistic asymptotics.
const assert=(cond,msg)=>{if(!cond)throw Error(msg);};
const gcd=(a,b)=>{while(b!==0n)[a,b]=[b,a%b];return a<0n?-a:a;};
const rat=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);const g=gcd(a,b);return [a/g,b/g];};
const plus=([a,b],[c,d])=>rat(a*d+b*c,b*d);
const minus=([a,b],[c,d])=>rat(a*d-b*c,b*d);
const times=([a,b],[c,d])=>rat(a*c,b*d);
const eq=([a,b],[c,d])=>a===c&&b===d;
const le=([a,b],[c,d])=>a*d<=b*c;
const zero=rat(0),one=rat(1);
let crossing=0, jointMesh=0, unweight=0, coefficients=0, expansion=0;
for(let u=1;u<=16;u++)for(let v=1;v<=16;v++)
for(let b=3;b<=16;b++)for(let a=1;a<=b;a++){
  // Both intervals have endpoint ratio 17/16.
  const L=16*u,U=17*u,l=16*v,V=17*v,aa=a*a,bb=b*b;
  if(L*bb>V*aa||U*bb<l*aa)continue;
  for(const r of [L,U])for(const s of [l,V]){
    assert(r*bb*17*17>=s*aa*16*16&&r*bb*16*16<=s*aa*17*17,"crossing rectangle envelope");
    crossing++;
  }
}
const primes=[11,13,17,19,23,29,31,37,41];
const den=primes.reduce((a,p)=>a*BigInt(p),1n);
const pairs=[];
for(const p of primes)for(const q of primes)if(p<=q)pairs.push([p,q,p*q,den/BigInt(q)]);
const abs=x=>x>=0n?x:-x;
for(let x=111;x<=1690;x+=19)for(let h=0;h<=75;h+=3)for(let l=0;l<=20;l++){
  const W=(d,a)=>pairs.reduce((s,[p,q,n,w])=>s+(x<n&&n<=x+d&&p*400<=q*a*a?w:0n),0n);
  const M=(d,a)=>BigInt(d*a)*den/1700n;
  const h0=h-h%11,h1=h0+11,l0=l-l%6,l1=Math.min(20,l0+6);
  const min=W(h0,l0),max=W(h1,l1), actual=W(h,l);
  assert(min<=actual&&actual<=max,"joint monotonicity");
  const lo=abs(min-M(h0,l0)),hi=abs(max-M(h1,l1));
  assert(abs(actual-M(h,l))<=(lo>hi?lo:hi)+M(h1,l1)-M(h0,l0),"two-parameter corner bracket");
  jointMesh+=2;
}
// Squares give rational square roots for testing the exact weight conversion;
// the identity for genuine primes follows from the same algebra.
for(let a=2;a<=32;a++)for(let b=a;b<=61;b++){
  const p=a*a,q=b*b,weight=rat(1,q), beta=rat(a,b), sqrtn=rat(a*b);
  assert(eq(times(weight,sqrtn),beta),"atom weight is balance divided by square root");
  assert(eq(times(weight,times(rat(b,a),sqrtn)),one),"exact unweighting");
  assert(eq(times(weight,weight),rat(p,q*p*q)),"squared weight identity");
  unweight+=3;
}
for(let a=0;a<=80;a++)for(let b=1;b<=29;b++){
  const A=rat(a,b), A2=times(A,A);
  const P=plus(A2,plus(times(rat(2),A),rat(2)));
  const dP=plus(times(rat(2),A),rat(2));
  assert(eq(minus(P,dP),A2),"derivative of the uniform second-order CDF term");
  coefficients++;
}
for(let L=2;L<=170;L++)for(let R=0;2*R<=L;R++){
  const z=rat(R,L), z2=times(z,z);
  const exact=rat(L*L,(L-R)*(L-R));
  const remainder=minus(exact,plus(one,times(rat(2),z)));
  const formula=times(times(z2,minus(rat(3),times(rat(2),z))),exact);
  assert(eq(remainder,formula),"Taylor remainder exact identity");
  assert(le(zero,remainder)&&le(remainder,times(rat(12),z2)),"uniform half-range Taylor bound");
  expansion+=2;
}
console.log({crossing,jointMesh,unweight,coefficients,expansion,
             total:crossing+jointMesh+unweight+coefficients+expansion});
