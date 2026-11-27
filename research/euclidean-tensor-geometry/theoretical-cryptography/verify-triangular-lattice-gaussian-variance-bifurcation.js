'use strict';
const assert=require('node:assert/strict');
let exact=0,num=0;
const eq=(a,b)=>{assert.equal(a,b);exact++;};
const pol=(p,q)=>p**4n+2n*p**3n*q+p*p*q*q-2n*p*q**3n-q**4n;
assert(pol(8832035n,10000000n)<0n&&pol(8832036n,10000000n)>0n);exact+=2;
const shell=[];
for(let m=-40;m<=40;m++)for(let n=-40;n<=40;n++){
  const q=m*m+n*n-m*n;
  assert(q!==2);eq(Math.abs((q-(m+n)*(m+n))%3),0);
  if(q===1)shell.push([m,n]);
}
eq(shell.length,6);
let n3=0;
for(let m=-3;m<=3;m++)for(let n=-3;n<=3;n++)if(m*m+n*n-m*n===3)n3++;
eq(n3,6);
const g=r=>r*r-(1+r)**2/(1+(1+r)**2);
function root(fun,l=.8,r=.99){
  assert(fun(l)<0&&fun(r)>0);
  for(let j=0;j<52;j++){const m=(l+r)/2;if(fun(m)>0)r=m;else l=m;}
  return (l+r)/2;
}
const r=root(g),a=r*r,c=(1+r)**2,d=1+c;
const K=d-a,A=2*c/d**2,B=-r*(1+(1+r)/d);
const h=2*K*A-4*B*B, gp=2*r-2*(1+r)/d**2,slope=-h/gp;
assert(h<0&&slope>2.30750&&slope<2.30751);num+=3;
function reduced(eta,r){
  let f=0,D2=0;const XY=[0,0], H=[0,0,0], J=[0,0,0];
  for(let m=-8;m<=8;m++)for(let n=-8;n<=8;n++){
    const q=m*m+n*n-m*n, s=(m+n)%2?-1:1, w=s*eta**q;
    const l=m*(1+r)-n,k=l*l,L=[m*m,m*n,n*n];
    f+=w;D2-=k*w;XY[0]-=l*m*w;XY[1]-=l*n*w;
    for(let j=0;j<3;j++){H[j]-=L[j]*w;J[j]+=k*L[j]*w;}
  }
  const [x,y,z]=J.map((v,i)=>(v/f-D2*H[i]/(f*f)-2*XY[i===2?1:0]*XY[i===0?0:1]/(f*f))/(2*eta));
  // x' coordinate is theta_3, and y' is theta_1. Then theta_2=-x'-y'.
  const xx=z, xy=z-y, yy=x-2*y+z;assert(yy<0);
  return xx-xy*xy/yy;
}
for(const eta of [1e-3,3e-4,1e-4,3e-5,1e-5]){
  assert(reduced(eta,r)<0);
  const v=root(r=>reduced(eta,r)); const diff=(v-r)/eta-slope;
  assert(v>r&&Math.abs(diff)<50*eta+1e-8);num+=3;
}
for(let k=0;k<=22;k++){
  const r=k/22,a=r*r,c=(1+r)**2;
  const x=g(r)<=0?1:((c/a)**2-1-c*c)/(2*c);
  const value=-a*x+Math.sqrt(1+c*c+2*c*x);
  for(let i=0;i<=40;i++)for(let j=0;j<=40;j++){
    const A=i*Math.PI/20,B=j*Math.PI/20;
    assert(-c*Math.cos(A)-Math.cos(B)-a*Math.cos(-A-B)<=value+1e-13);num++;
  }
}
console.log('PASS',exact,'exact algebra checks and',num,'numeric comparisons');
