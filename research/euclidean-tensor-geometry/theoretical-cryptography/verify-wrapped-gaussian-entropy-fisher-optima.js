'use strict';
const assert=require('node:assert/strict');
let exact=0,numerical=0;
const minShell=[[1,0],[0,1],[-1,1],[-1,0],[0,-1],[1,-1]];
const q=(i,j)=>i*i+i*j+j*j;
for(let x=-15;x<=15;x++) for(let y=-15;y<=15;y++){
  const values=minShell.map(([i,j])=>{
    const a=2*i+j,b=j;return (a*a-3*b*b)*x+6*a*b*y;
  });
  assert.equal(values.reduce((p,a)=>p+a,0),0);
  assert.equal(values.reduce((p,a)=>p+a*a,0),48*(x*x+3*y*y));
  assert((x===0&&y===0)||Math.min(...values)<0);exact+=3;
}
let min=Infinity;
const P=[];
for(let i=-8;i<=8;i++)for(let j=-8;j<=8;j++)if(i||j)P.push([i,j,q(i,j)]);
for(const [i,j,r] of P) for(const [k,l,s] of P)if(i!==k||j!==l){
  const pair=2*(r+s)+q(i-k,j-l);
  assert(pair>=5);
  assert.equal(pair,3*(r+s)-(2*i*k+i*l+j*k+2*j*l));
  min=Math.min(min,pair);exact+=2;
}
assert.equal(min,5);exact++;
// These quadrature checks are not used to certify the theorem.
const pi=Math.PI,m=2/Math.sqrt(3),s=Math.sqrt(m);
const bases=(x,y)=>[s*(x+y/2),s*Math.sqrt(3)*y/2];
function act([u,v],a,b,time){
  const r=Math.hypot(a,b),C=Math.cosh(time*r/2),S=r?Math.sinh(time*r/2)/r:0;
  return [C*u+S*(a*u+b*v),C*v+S*(b*u-a*v)];
}
const E=([u,v],a,b)=>a*(u*u-v*v)+2*b*u*v;
function early(t,a,b,N=104){
  let H=0,Q00=0,Q01=0,Q11=0;
  const shifts=[];
  for(let k=-3;k<=3;k++)for(let l=-3;l<=3;l++)shifts.push(act(bases(k,l),a,b,t));
  for(let i=0;i<N;i++)for(let j=0;j<N;j++){
    const [x,y]=act(bases((i+.5)/N-.5,(j+.5)/N-.5),a,b,t);
    const values=shifts.map(([k,l])=>{
      const X=x+k,Y=y+l;
      return [X,Y,(X*X+Y*Y)/(4*t)];
    });
    const L=Math.min(...values.map(v=>v[2])), F=Math.exp(-L)/(4*pi*t*N*N);
    let w=0,r=0,Xbar=0,Ybar=0;
    for(const [X,Y,d] of values){const mass=Math.exp(L-d);w+=mass;r+=mass*(d-L);Xbar+=mass*X;Ybar+=mass*Y;}
    Xbar/=w;Ybar/=w;H+=F*(r+w*Math.log(w));
    for(const [X,Y,d] of values){
      const weight=F*Math.exp(L-d)/(2*t), xx=X-Xbar,yy=Y-Ybar;
      Q00+=weight*xx*xx;Q01+=weight*xx*yy;Q11+=weight*yy*yy;
    }
  }
  const tr=Q00+Q11, defect=tr-Q00*Q11+Q01*Q01;
  const d=defect/(1+Math.sqrt(1-defect));
  return [H*Math.exp(m/(16*t))/Math.sqrt(t), d*Math.exp(m/(16*t))*Math.sqrt(t)];
}
function late(A,a,b,N=66) {
  const modes=[];
  for(let i=-5;i<=5;i++)for(let j=-5;j<=5;j++)if(i||j){
    const [X,Y]=act(bases(i,j),a,b,1/A);
    modes.push([i,j,Math.exp(-A*(X*X+Y*Y))]);
  }
  let ent=0;
  for(let i=0;i<N;i++)for(let j=0;j<N;j++){
    let u=0;
    for(const [k,l,c] of modes)u+=c*Math.cos(2*pi*(k*(i+.5)/N+l*(j+.5)/N));
    ent+=((1+u)*Math.log1p(u)-u)/N/N;
  }
  return ent*Math.exp(2*A*m);
}
const shape=[[0,0],[2,1],[-3,2],[0,-5],[6,-1]];
for(const [a,b] of shape){
  const F=minShell.reduce((s,v)=>s+Math.exp(-E(bases(...v),a,b)/16),0);
  const f0=2*Math.sqrt(pi/m)*F,f1=Math.sqrt(pi*m)/8*F;
  let last=[Infinity,Infinity];
  for(const t of [.008,.0065,.005]){
    const p=early(t,a,b),err=[Math.abs(p[0]/f0-1),Math.abs(p[1]/f1-1)];
    assert(err[0]<0.15&&err[1]<0.09);
    assert(err[0]<last[0]&&err[1]<last[1]);last=err;numerical+=4;
  }
  if(a||b){assert(F>6);numerical++;}
  for(const A of [4,8,16]){
    const A0=a/12,B0=b/12;
    const L0=minShell.reduce((s,v)=>s+Math.exp(-2*E(bases(...v),A0,B0)),0)/2;
    assert(Math.abs(late(A,A0,B0)/L0-1)<0.08);numerical++;
  }
}
console.log('PASS',exact,'integer checks and',numerical,'quadrature checks');
