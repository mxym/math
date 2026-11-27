'use strict';

// Exact rationals in Q[s], s^2=1/10. Rational c values use zero s part.
const assert = require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;
const R=(a,b=0n,d=1n)=>{
  a=BigInt(a);b=BigInt(b);d=BigInt(d);if(d<0n)[a,b,d]=[-a,-b,-d];
  assert(d>0n);const g=gcd(gcd(a,b),d);return [a/g,b/g,d/g];
};
const Q=(a,d=1)=>R(a,0,d), O=Q(0), I=Q(1), S=R(0,1);
const add=([a,b,d],[e,f,g])=>R(a*g+e*d,b*g+f*d,d*g);
const mul=([a,b,d],[e,f,g])=>R(10n*a*e+b*f,10n*(a*f+b*e),10n*d*g);
const neg=([a,b,d])=>R(-a,-b,d);
const sub=(a,b)=>add(a,neg(b));
const inv=([a,b,d])=>R(10n*a*d,-10n*b*d,10n*a*a-b*b);
const div=(a,b)=>mul(a,inv(b));
const sq=a=>mul(a,a), pow=(a,k)=>k?mul(a,pow(a,k-1)):I;
const sum=a=>a.reduce(add,O);
const rationalSign=v=>{assert.equal(v[1],0n);return Math.sign(Number(v[0]));};
let checks=0;
const same=(a,b)=>{assert.deepEqual(a,b);checks++;};
const key=(i,j)=>i+','+j, mode=k=>k.split(',').map(Number), z=key(0,0);
const addF=(a,b)=>{const m=new Map(a);for(const [k,v] of b)m.set(k,add(m.get(k)||O,v));return m;};
const scale=(a,c)=>new Map([...a].map(([k,v])=>[k,mul(v,c)]));
const product=(a,b)=>{
  const m=new Map();
  for(const [x,u] of a)for(const [y,v] of b){
    const [i,j]=mode(x),[k,l]=mode(y), t=key(i+k,j+l);
    m.set(t,add(m.get(t)||O,mul(u,v)));
  }
  return m;
};
const mean=a=>a.get(z)||O, dot=(a,b)=>mean(product(a,b));
const cos=(a,b)=>new Map([[key(1,0),div(a,Q(2))],[key(-1,0),div(a,Q(2))],
  [key(0,1),div(b,Q(2))],[key(0,-1),div(b,Q(2))]]);
const inverse=(a,c)=>new Map([...a].filter(([k])=>{
  const [m,n]=mode(k);return m*m+n*n>1;
}).map(([k,v])=>{const [m,n]=mode(k);return [k,div(v,add(Q(m*m+n*n-1),mul(Q(2*m*n),c)))];}));
function expansion(a,b,c) {
  const g=cos(a,b), g2=product(g,g), g3=product(g2,g),g4=product(g2,g2);
  const h=scale(inverse(g2,c),Q(1,2)),p=addF(scale(product(g,h),Q(-4)),scale(g3,Q(2,3)));
  const g22=sq(mean(g2)), h2=product(h,h), k=scale(inverse(p,c),Q(-1,4));
  const hmean=mean(h2);
  const qua=sum([mul(Q(1,6),mean(g4)),mul(Q(1,2),g22),mul(Q(-1,2),dot(g2,inverse(g2,c)))]);
  const six=[
    mul(Q(-2,3),dot(h,h2)),dot(g2,h2),mul(Q(-1,3),dot(g4,h)),
    mul(Q(1,30),dot(g3,g3)),mul(mean(g2),hmean),
    mul(Q(-1,6),pow(mean(g2),3)),mul(Q(-1,8),dot(p,inverse(p,c)))
  ];
  return {qua,six,g,h,k};
}
for (const c of [Q(0),Q(1,12),Q(1,6),Q(3,10),S,Q(1,3),Q(7,20),Q(6,13)]) {
  for(let a=-2;a<=3;a++)for(let b=-2;b<=3;b++){
    const {qua}=expansion(Q(a),Q(b),c);
    const expected=sub(Q(a**4+b**4,6),div(mul(Q(2*a*a*b*b),sq(c)),sub(I,mul(Q(4),sq(c)))));
    same(qua,expected);
  }
}
const crit=expansion(I,I,S);
same(crit.qua,O);
const six=[Q(-5,72),Q(191,144),Q(-8,9),Q(5,24),Q(47,48),Q(-1,6),Q(-85,324)];
for(let j=0;j<six.length;j++)same(crit.six[j],six[j]);
same(sum(crit.six),Q(365,324));
const poly=c=>sum([Q(4),mul(Q(-72),c),mul(Q(89),sq(c)),mul(Q(-12),pow(c,3)),mul(Q(-12),pow(c,4))]);
const acoef=c=>sum([Q(2),mul(Q(-6),c),mul(Q(4),sq(c))]);
const low=c=>sub(sub(Q(2,3),mul(Q(1,2),c)),div(sq(sum([Q(2),c,mul(Q(-2),sq(c))])),mul(Q(4),acoef(c))));
same(low(Q(1,18)),Q(149,11016));
assert(rationalSign(poly(Q(1,18)))>0);assert(rationalSign(poly(Q(3,50)))<0);checks+=2;
for(let m=-40;m<=40;m++)for(let n=-40;n<=40;n++){
  if(!m||!n) continue;
  const q=m*m+n*n, ab=Math.abs(m*n), P=m**4+n**4-q;
  assert.equal(2*P+6*ab**2-2*ab*(2*q-1),2*(q-ab)*(q-ab-1));checks++;
  assert(q-ab>=1);checks++;
}
for(let j=0;j<=110;j++){
  const c=Q(j,2000), a=acoef(c);assert(rationalSign(a)>0);
  assert(rationalSign(sub(Q(4,3),div(mul(Q(4),sq(sub(I,sq(c)))),a)))<0);
  for(const sgn of [-1,1]) {
    const s=Q(sgn,2), val=sub(sum([mul(Q(4,3),sq(s)),Q(1,3),mul(c,s)]),
      div(sq(add(mul(mul(Q(-4),sub(I,sq(c))),s),c)),mul(Q(4),a)));
    assert(rationalSign(val)>0);checks++;
  }checks+=2;
}
// Independent midpoint-grid integral of f^2 log f^2 and the exact Fourier energy.
const toNum=([a,b,d])=>(Number(a)+Number(b)/Math.sqrt(10))/Number(d);
function numerical(c,t,optThird=true){
  const {g,h,k}=expansion(I,I,c), fs=[g,h,...(optThird?[k]:[])];
  const entries=fs.flatMap((a,i)=>[...a].map(([v,r])=>[mode(v),toNum(r)*t**(i+1)]));
  const coeff=new Map();
  for(const [v,r] of entries)coeff.set(key(...v),(coeff.get(key(...v))||0)+r);
  let en=0,m2=0,ent=0;const C=toNum(c),N=104;
  for(const [v,r] of coeff){let [m,n]=mode(v);en+=(m*m+n*n+2*C*m*n)*r*r;m2+=r*r;}
  for(let j=0;j<N;j++)for(let l=0;l<N;l++){
    const x=2*Math.PI*(j+0.5)/N,y=2*Math.PI*(l+0.5)/N;
    let u=0;for(const [v,r] of coeff){const [m,n]=mode(v);u+=r*Math.cos(m*x+n*y);}
    assert(1+u>0);
    ent+=2*(1+u)**2*Math.log1p(u)-2*u;
  }
  return 2*en-(ent/N/N-(1+m2)*Math.log1p(m2));
}
for(const t of [0.07,0.045,0.026]){
  let d=numerical(Q(7,20),t,false);
  assert(d<0);assert(Math.abs(d/t**4-toNum(expansion(I,I,Q(7,20)).qua))<0.015);
  d=numerical(S,t,true);
  assert(d>0);assert(Math.abs(d/t**6-365/324)<0.07);
  checks+=4;
}
console.log('PASS',checks,'exact/coefficient and numerical sanity checks');
