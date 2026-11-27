"use strict";
// Fixed small arithmetic fixtures. None of these checks assumes RH or LI, or
// attempts to estimate the zeta/Dirichlet L-function zeros.
const assert=(ok,m)=>{if(!ok)throw Error(m);};
const prime=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];
const chi=p=>p%4===1?1:-1;
const gcd=(a,b)=>{while(b){[a,b]=[b,a%b];}return a>=0n?a:-a;};
const r=(a,b=1n)=>{
  a=BigInt(a);b=BigInt(b);
  if(b<0n){a=-a;b=-b;}
  const g=gcd(a,b);return [a/g,b/g];
};
const add=([a,b],[c,d])=>r(a*d+b*c,b*d);
const neg=([a,b])=>[-a,b];
const mul=([a,b],[c,d])=>r(a*c,b*d);
const inv=([a,b])=>r(b,a);
const div=(a,b)=>mul(a,inv(b));
const eq=([a,b],[c,d])=>a===c&&b===d;
const zero=r(0),one=r(1);
const C=(a,b=zero)=>[a,b];
const conj=([a,b])=>[a,neg(b)];
const Add=([a,b],[c,d])=>[add(a,c),add(b,d)];
const Mul=([a,b],[c,d])=>[add(mul(a,c),neg(mul(b,d))),add(mul(a,d),mul(b,c))];
const Inv=([a,b])=>{
  const n=add(mul(a,a),mul(b,b));return [div(a,n),neg(div(b,n))];
};
const Eq=([a,b],[c,d])=>eq(a,c)&&eq(b,d);
let expansions=0, partialSummation=0, multipliers=0, moments=0, inversions=0;

for(const [a,b] of [[1,3],[2,5],[1,5],[3,7],[2,9]])for(let x=41;x<=3600;x+=13) {
  let N=0,M=0,T1=0,T2=0,T3=0;
  for(const p of prime)for(const q of prime)if(p<q&&p*q<=x&&BigInt(p)**BigInt(b)>BigInt(x)**BigInt(a)){
    N++;M+=Number(chi(p)===-1&&chi(q)===-1);T1+=chi(p);T2+=chi(q);T3+=chi(p)*chi(q);
  }
  assert(4*M-N===-T1-T2+T3,"unrestricted sign expansion inside an exact cutoff");
  expansions++;
}
const S=t=>prime.filter(p=>p<=t).reduce((z,p)=>z+chi(p),0);
for(let l=2;l<=60;l++)for(let u=l+1;u<=100;u++)for(const power of [1,2,3]){
  const g=t=>r(1n,BigInt(t)**BigInt(power));
  const events=prime.filter(p=>l<p&&p<=u);
  const left=events.reduce((s,p)=>add(s,mul(r(-chi(p)),g(p))),zero);
  let right=add(mul(r(S(l)),g(l)),mul(r(-S(u)),g(u)));
  const list=[l,...events.filter(p=>p<u),u];
  for(let j=0;j+1<list.length;j++)
    right=add(right,mul(r(S(list[j])),add(g(list[j+1]),neg(g(list[j])))));
  assert(eq(left,right),"signed endpoint and integration by parts");
  partialSummation++;
}

function pack(x){return x.join(",");}
function unpack(x){return x.split(",").map(Number);}
function get(M,k){return M.get(k)??C(zero);}
function accumulate(M,k,c){M.set(k,Add(get(M,k),c));}
function multPoly(P,Q){
  const out=new Map();
  for(const [k,a] of P)for(const [l,b] of Q){
    const y=unpack(l);
    const v=unpack(k).map((u,j)=>u+y[j]);
    accumulate(out,pack(v),Mul(a,b));
  }
  return out;
}
function pol(coeff,pow){
  const p=new Map(), v=Array(coeff.length).fill(0);
  for(const [j,b] of coeff.entries()){
    v[j]=pow;accumulate(p,pack(v),b);
    v[j]=-pow;accumulate(p,pack(v),conj(b));v[j]=0;
  }
  return p;
}
const half=r(1,2);
for(let j=0;j<=51;j++)for(let k=1;k<=17;k++){
  const t=r(j,k), rho=C(half,t);
  const b=Inv(conj(rho));
  const filter=Add(C(neg(one)),b);
  assert(Eq(Mul(filter,Inv(rho)),b),"one-sided multiplier conjugates the coefficient");
  multipliers++;
}
for(let K=1;K<=17;K++) {
  const coeff=[], zeroKey=pack(Array(K).fill(0));
  let expected=zero;
  for(let j=1;j<=K;j++){
    const t=r(3*j+1,7+j);
    const d=add(mul(t,t),mul(half,half));
    expected=add(expected,inv(mul(d,d)));
    coeff.push(Inv(C(half,neg(t))));
  }
  const f=pol(coeff,1),g=pol(coeff,2);
  assert(Eq(get(multPoly(f,g),zeroKey),C(zero)),"mixed covariance");
  const mix=get(multPoly(multPoly(f,f),g),zeroKey);
  assert(Eq(mix,C(expected)),"nonzero mixed moment");
  moments+=2;
}
// A one-parameter torus with arithmetic relations among formal frequencies:
// Laurent inversion preserves every constant coefficient of a polynomial.
for(let a=1;a<=11;a++)for(let b=1;b<=7;b++){
  const f=new Map();
  accumulate(f,pack([a]),C(r(2,3),r(5,7)));
  accumulate(f,pack([-a]),C(r(2,3),r(-5,7)));
  accumulate(f,pack([b]),C(r(3,5),r(1,2)));
  accumulate(f,pack([-b]),C(r(3,5),r(-1,2)));
  let p=f, q=new Map([...f].map(([x,c])=>[pack(unpack(x).map(y=>-y)),c])), v=q;
  for(let d=1;d<=4;d++){
    assert(Eq(get(p,pack([0])),get(v,pack([0]))),"inversion of an orbit with frequency relations");
    p=multPoly(p,f);v=multPoly(v,q);
    inversions++;
  }
}
console.log({expansions,partialSummation,multipliers,moments,inversions,
             total:expansions+partialSummation+multipliers+moments+inversions});
