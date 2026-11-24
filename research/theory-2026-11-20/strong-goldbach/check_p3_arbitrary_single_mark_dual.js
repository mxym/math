const Q=(n,d=1n)=>[BigInt(n),BigInt(d)];
const add=([n,d],[m,e])=>Q(n*e+m*d,d*e), mul=([n,d],[m,e])=>Q(n*m,d*e);
const sub=(a,[m,e])=>add(a,Q(-m,e)); const div=([n,d],[m,e])=>Q(n*e,d*m);
const gt=([n,d],[m,e])=>n*e>m*d;
function logbounds(x,M=10){const a=div(sub(x,Q(1)),add(x,Q(1))), a2=mul(a,a);let term=a,l=Q(0);for(let k=0;k<M;k++){l=add(l,div(term,Q(2*k+1)));term=mul(term,a2);} l=mul(Q(2),l); return [l,add(l,div(mul(Q(2),term),mul(Q(2*M+1),sub(Q(1),a2))))];}
const [lo2,hi2]=logbounds(Q(2)), [lo116]=logbounds(Q(11,6));
const H16=Array.from({length:16},(_,i)=>Q(1,i+1)).reduce(add,Q(0));
const g=Q(5768,10000); if(!gt(sub(sub(H16,mul(Q(4),hi2)),Q(1,32)),g))throw Error("gamma");
let e=Q(1), term=Q(1);for(let i=1;i<=8;i++){term=div(mul(term,g),Q(i));e=add(e,term);}
if(!gt(e,Q(500,281)))throw Error("Euler factor");
const floor=add(mul(Q(2),add(mul(Q(4),lo2),lo116)),Q(266,100));
if(!gt(floor,div(Q(281,1000),Q(3,100))))throw Error("critical endpoint");
if(!gt(mul(Q(281,1000),sub(Q(1,4),Q(7,100))),mul(Q(1,2),Q(7,100))))throw Error("derivative");
console.log("PASS");
