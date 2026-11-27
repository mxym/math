'use strict';
const assert = require('node:assert/strict');
let exact = 0, numeric = 0;
function chk(x) { assert(x); exact++; }
function near(x,y,tol=1e-10) { assert(Number.isFinite(x) && Math.abs(x-y)<=tol, [x,y,tol].join(' ')); numeric++; }
const mk = (a,b,d)=>[[BigInt(a),BigInt(b)],[BigInt(b),BigInt(d)]];
const I = mk(1,0,1);
const mp = (A,B)=>A.map((r,i)=>r.map((_,j)=>r[0]*B[0][j]+r[1]*B[1][j]));
const plus = (A,B)=>A.map((r,i)=>r.map((x,j)=>x+B[i][j]));
const sc = (A,t)=>A.map(r=>r.map(x=>x*t));
const sub = (A,B)=>plus(A,sc(B,-1n));
const tr = A=>[[A[0][0],A[1][0]],[A[0][1],A[1][1]]];
const det = A=>A[0][0]*A[1][1]-A[0][1]*A[1][0];
const adj = A=>[[A[1][1],-A[0][1]],[-A[1][0],A[0][0]]];
const eq = (A,B)=>A.every((r,i)=>r.every((v,j)=>v===B[i][j]));
const pos = A=>eq(A,tr(A))&&A[0][0]>0n&&det(A)>0n;
const form = (A,x,y)=>A[0][0]*x*x+(A[1][0]+A[0][1])*x*y+A[1][1]*y*y;
function shortest(A) {
  let best = A[0][0]<A[1][1]?A[0][0]:A[1][1], shell = [];
  const trace=A[0][0]+A[1][1], delta=det(A);
  let R=1n;
  while ((R+1n)**2n*delta<=best*trace) R++;
  for(let x=-R;x<=R;x++) for(let y=-R;y<=R;y++) {
    if(x===0n&&y===0n) continue;
    const v=form(A,x,y);
    if(v<best) {best=v;shell=[];}
    if(v===best)shell.push([x,y]);
  }
  return {best,shell};
}
const all = [];
for(let a=1;a<=4;a++) for(let b=-2;b<=2;b++) for(let d=1;d<=4;d++){
  const A=mk(a,b,d);if(pos(A))all.push(A);
}
let noncommuting=0;
for(const A of all) for(const B of all) {
  if(!eq(mp(A,B),mp(B,A)))noncommuting++;
  const S=plus(A,B), den=det(S), a=det(A),b=det(B);
  const M=mp(B,adj(S)), C=mp(M,A);
  chk(pos(C)&&pos(sub(sc(A,den),C))&&pos(sub(sc(B,den),C)));
  chk(det(C) === a*b*den);
  chk(eq(mp(plus(sc(adj(A),b),sc(adj(B),a)),C),sc(I,den*a*b)));
  const W=plus(sc(A,den),C);
  chk(pos(sub(sc(W,den*den),mp(mp(M,W),tr(M)))));
  const {best:alpha}=shortest(A);
  const {best:beta,shell}=shortest(W);
  chk(den*alpha<beta && beta<2n*den*alpha);
  for(const [x,y] of shell){
    const u0=M[0][0]*x+M[1][0]*y,u1=M[0][1]*x+M[1][1]*y;
    chk(u0%den!==0n||u1%den!==0n);
  }
}
chk(noncommuting>1000);

const gcd=(m,n)=>n?gcd(n,m%n):m;
const mod=(x,q)=>(x%q+q)%q;
for(let q=2;q<=17;q++) for(let p=1;p<q;p++) {
  if(gcd(p,q)!==1) continue;
  for(let b=1;b<=12;b++) for(let a=-b;a<=b;a++){
    const points = Array.from({length:q},(_,k)=>mod((q-p)*a+p*b*k,q*b));
    chk(new Set(points).size===q);
    const exactByLevelSet=points.every(u=>u===points[0]||u===mod(-points[0],q*b));
    chk(exactByLevelSet === (q===2&&mod(2*a,2*b)===b));
  }
}

const PI=Math.PI, TAU=2*PI;
const gauss=(T,x)=>Math.exp(-PI*x*x/T)/Math.sqrt(T);
const thetaU=(T,v)=>{
  let z=0;
  for(let m=1;m<=24;m++)z+=2*Math.exp(-PI*T*m*m)*Math.cos(TAU*m*v);
  return z;
};
function simpson(fun,lo,hi,N=2048) {
  const step=(hi-lo)/N;
  let sum=fun(lo)+fun(hi);
  for(let i=1;i<N;i++)sum+=(i%2?4:2)*fun(lo+i*step);
  return sum*step/3;
}
function direct(A,B,d,k) {
  const radius=8*Math.sqrt(B), R=Math.ceil(Math.abs(d)+radius+8*Math.sqrt(A))+1;
  return simpson(y=>{
    let den=0;
    for(let j=-R;j<=R;j++)den+=gauss(A,j-y);
    return gauss(B,y-d)*gauss(A,k-y)/den;
  },d-radius,d+radius);
}
function posterior(A,B,d,k) {
  const S=A+B,C=A*B/S,v=(A*d+B*k)/S,radius=8*Math.sqrt(C);
  return gauss(S,k-d)*simpson(w=>gauss(C,w)/(1+thetaU(A,v+w)),-radius,radius);
}
for(const [A,B,d] of [[0.08,0.13,0],[0.11,0.29,0.17],[0.21,0.65,0.88],
                     [0.27,0.33,-0.5],[1,2,0.26],[0.56,0.56,0.12],
                     [0.08,0.08,0.5],[0.31,0.31,-0.5],[0.8,0.8,1.5],
                     [1.21,1.21,-1.5],[2.8,2.8,0.5],[5.3,5.3,0.5]]) {
  const data=[];
  for(let k=-8;k<=8;k++) {
    const p=direct(A,B,d,k),q=gauss(A+B,k-d)/(1+thetaU(A+B,d));
    near(p,posterior(A,B,d,k),5e-12);
    if(A===B && mod(2*d,2)===1) near(p,q,5e-12);
    data.push([p,q]);
  }
  const tv=data.reduce((acc,[p,q])=>acc+Math.abs(p-q),0)/2;
  const e=T=>thetaU(T,0);
  if(e(A)<1)chk(tv <= (1+e(A))*(e(A+A*B/(A+B))+e(A)**2/(1-e(A)))+1e-12);
}
// Leading coefficient: use the nonconstant reciprocal correction directly to
// avoid loss of significance; the heat operator acts by exact mode multipliers.
for(const [p,q] of [[1,2],[1,3],[2,3],[1,4],[3,4],[2,5],[3,5]]) {
  for(const d of [0,0.14,0.25,0.5,0.67]) {
    let h2=0,abs=0;
    for(let k=0;k<q;k++){
      const h=2*Math.cos(TAU*((1-p/q)*d+p*k/q));
      abs+=Math.abs(h)/(2*q);h2+=h*h/q;
    }
    near(h2,q===2?4*Math.cos(PI*d)**2:2,1e-12);
    const A=50,B=A*p/(q-p),S=A+B,C=A*B/S,scale=Math.exp(-PI*(A+C));
    const freq=[];
    for(let m=0;m<=8;m++){
      let cm=0;
      for(let j=0;j<256;j++){
        const v=j/256,u=thetaU(A,v);
        cm+=(-u/(1+u))*Math.cos(TAU*m*v)/256;
      }
      freq.push(m===0?cm:2*(cm*Math.exp(-PI*C*m*m)/scale));
    }
    const val=[],wt=[];
    const R=Math.ceil(Math.abs(d)+8*Math.sqrt(S)), norm=1+thetaU(S,d);
    for(let k=-R;k<=R;k++){
      const v=((1-p/q)*d+p*k/q);
      val.push(freq.slice(1).reduce((r,f,i)=>r+f*Math.cos(TAU*(i+1)*v),0));
      wt.push(gauss(S,k-d)/norm);
    }
    const mean=val.reduce((r,v,i)=>r+wt[i]*v,0);
    const center=1+freq[0]+scale*mean;
    const ratio=val.map(v=>(v-mean)/center);
    const tv=ratio.reduce((r,v,i)=>r+wt[i]*Math.abs(v)/2,0);
    const chi=ratio.reduce((r,v,i)=>r+wt[i]*v*v,0);
    near(tv,abs,4e-4);
    near(chi,h2,1e-3);
  }
}
console.log('PASS: '+exact+' exact and '+numeric+' numerical checks; '+noncommuting+' noncommuting matrix pairs');
