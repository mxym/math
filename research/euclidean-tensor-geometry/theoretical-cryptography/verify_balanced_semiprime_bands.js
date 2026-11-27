"use strict";

// Exact rational geometry on fixed small grids, with no external inputs.
const Q=(n,d=1n)=>({n:BigInt(n),d:BigInt(d)});
const mul=(a,b)=>Q(a.n*b.n,a.d*b.d);
const div=(a,b)=>Q(a.n*b.d,a.d*b.n);
const sub=(a,b)=>Q(a.n*b.d-b.n*a.d,a.d*b.d);
const cmp=(a,b)=>a.n*b.d-b.n*a.d;
const eq=(a,b)=>cmp(a,b)===0n;
const lt=(a,b)=>cmp(a,b)<0n;
const le=(a,b)=>cmp(a,b)<=0n;
const inside=(v,lo,hi)=>lt(lo,v)&&le(v,hi);
let checks=0,pairs=0,cumulative=0,short=0,nontrivial=0;
function ok(x,msg) { checks++; if(!x)throw Error(msg); }
const prime=[11,13,17,19,23,29,31,37,41,43,47,53].map(p=>Q(p));
for(const [x,k] of [[173,83],[247,160],[437,200],[539,301],
                     [667,97],[899,530],[1147,135],[1591,373],[1999,622]]) {
  const x0=Q(x), cap=Q(x+k), A=Q(11), B=Q(38);
  for(const [a,c] of [[Q(1),Q(5,4)],[Q(21,20),Q(3,2)],
                      [Q(3,2),Q(8,5)],[Q(17,8),Q(7,3)]]) {
    for(const den of [12,16,24,100]) {
      const m=Q(den+1,den), m2=mul(m,m);
      const levels=[m,Q(2*den+1,2*den),Q(4*den+1,4*den)];
      for(const p of prime) for(const q of prime) {
        const n=mul(p,q), rho=div(q,p);
        const trueRatio=inside(rho,a,c);
        const trueCum=trueRatio&&inside(p,A,B)&&le(n,x0);
        const trueShort=trueRatio&&inside(n,x0,cap);
        for(const mp of levels) for(const mq of levels) {
          const t=div(p,mp), v=div(q,mq), z=mul(t,v), r=div(v,t);
          ok(lt(t,p)&&le(p,mul(m,t))&&lt(v,q)&&le(q,mul(m,v)),
             "averaging box");
          ok(le(z,n)&&le(n,mul(z,m2)),"product expansion");
          ok(le(div(r,m),rho)&&le(rho,mul(r,m)),"ratio expansion");
          ok(eq(div(p,div(p,m)),m),"constant log-normalization");
          const ep=inside(r,div(a,m),mul(c,m));
          const em=inside(r,mul(a,m),div(c,m));
          const outerCum=ep&&inside(t,div(A,m),B)&&le(z,x0);
          const innerCum=em&&inside(t,A,div(B,m))&&le(z,div(x0,m2));
          const outerShort=ep&&inside(z,div(x0,m2),cap);
          const innerShort=em&&inside(z,x0,div(cap,m2));
          ok(!trueCum||outerCum,"cumulative inclusion");
          ok(!innerCum||trueCum,"cumulative erosion");
          ok(!trueShort||outerShort,"short-band inclusion");
          ok(!innerShort||trueShort,"short-band erosion");
          if(trueCum)cumulative++;
          if(trueShort)short++;
          if(innerCum||innerShort)nontrivial++;
          // Analytic determinant of (t,v) -> (tv, log(v/t)):
          // d(tv)/dt=v, d(tv)/dv=t, d(log(v/t))/dt=-1/t, ... /dv=1/v.
          const determinant=sub(mul(v,div(Q(1),v)),mul(t,div(Q(-1),t)));
          ok(eq(determinant,Q(2)),"product/log-ratio Jacobian");
          pairs++;
        }
      }
    }
  }
}
ok(cumulative>0&&short>0&&nontrivial>0,"nonvacuous geometric cases");
// A thin off-diagonal band can contain an integer even at length <1.
const p=Q(41), q=Q(53), r2=div(q,p), r1=sub(r2,Q(1,10000));
ok(lt(mul(sub(r2,r1),p),Q(1))&&inside(div(q,p),r1,r2),
   "small-coordinate rounding term");
console.log("OK: "+checks+" exact checks; "+pairs+" smoothing samples, "+
            cumulative+" cumulative-band and "+short+" short-band hits.");
