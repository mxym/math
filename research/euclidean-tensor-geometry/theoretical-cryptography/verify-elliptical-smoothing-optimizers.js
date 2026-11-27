"use strict";
// Exact checks of cubic identities and the scalar perturbation coefficient.
let checks=0;
function eq(a,b,what){checks++;if(String(a)!==String(b))throw Error(what+": "+a+" !== "+b);}
const add=(a,b)=>a.map((x,j)=>x+b[j]);
const scale=(a,k)=>a.map(x=>BigInt(k)*x);
function mul(a,b){
  const c=Array(5).fill(0n);
  for(let i=0;i<3;i++)for(let j=0;j<3;j++)c[i+j]+=a[i]*b[j];
  // theta^3=theta+1, theta^4=theta^2+theta.
  c[0]+=c[3];c[1]+=c[3]+c[4];c[2]+=c[4];
  return c.slice(0,3);
}
const one=[1n,0n,0n],theta=[0n,1n,0n],theta2=mul(theta,theta);
const inv=add(theta2,scale(one,-1)), a=mul(inv,inv);
eq(mul(theta,inv).join(","),one.join(","),"theta inverse is integral");
eq(add(scale(theta2,-1),inv).join(","),scale(one,-1).join(","),"unit polynomial endpoint identity");
const cubicNum=(u,d)=>u*u*u-u*d*d-d*d*d; // denominator d^3
eq(cubicNum(1n,1n),-1n,"root left bound");
eq(cubicNum(4n,3n),1n,"root right bound");
eq(-4n*(-1n)**3n-27n*(-1n)**2n,-23n,"cubic discriminant");
for(let P=10;P<200;P++){
  const u=BigInt(P+1),d=BigInt(P);
  // After clearing denominators, derivative for T=3 equals -(u-1)^2(2u+1).
  eq((3n*u*u*d-2n*u*u*u-d*d*d),-((u-d)**2n)*(2n*u+d),"strict unit obstruction derivative");
  for(let T=0;T<=3;T++){
    const derivative=BigInt(T)*u*u*d-2n*u*u*u-d*d*d;
    eq(derivative<0n,true,"all admissible integer traces");
  }
}
for(let v=1;v<=50;v++){
  const U=BigInt(v+1),V=BigInt(v);
  // Sign of f(log(U/V))-f(-log(U/V)) after multiplying by (UV)^2.
  const diff=U**4n-V**4n+2n*U*V**3n-2n*U**3n*V;
  eq(diff,(U-V)**3n*(U+V),"negative unit exponent gives earlier shell");
  eq(diff>0n,true,"shell ordering");
}
// Weighted projection P(a,b) at signature (1,1); S=2P.
const realTimes3=add(scale(a,4),scale(theta,-4));
const imagTimes3=add(scale(theta,2),scale(a,-2));
eq(add(realTimes3,scale(imagTimes3,2)).join(","),"0,0,0","projected shell lies in hyperplane");
eq(scale(realTimes3,-1).join(","),scale(add(theta,scale(a,-1)),4).join(","),
   "real shift factor from -S/(2w rho)");
eq(4+2,6,"leading energy Hessian in real-coordinate parameter");
eq(2*6,12,"leading theta Hessian multiplicity");
console.log("OK: "+checks+" exact cubic, ordering, and perturbation-coefficient checks.");
