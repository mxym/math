'use strict';
/* Fixed synthetic noise fixtures; exact energies and separate numerical
 * regression. No reads, writes, data inputs, or packages. */
const assert=require('node:assert/strict');
const seq=n=>Array.from({length:n},(_,i)=>i);
const zz=n=>seq(2*n+1).map(i=>i-n);
const sum=a=>a.reduce((x,y)=>x+y,0);
let exact=0,numerical=0;
function ck(a,b){assert.deepEqual(a,b);exact++;}
function tr(v){assert(v);exact++;}
function near(a,b,e=2e-12){assert(Math.abs(a-b)<=e*Math.max(1,Math.abs(a),Math.abs(b)),String([a,b]));numerical++;}
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a;}
function rat(n,d=1n){if(d<0n){d=-d;n=-n;}const g=gcd(n,d);return [n/g,d/g];}
const Q=n=>rat(BigInt(n)), plus=(a,b)=>rat(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const minus=(a,b)=>plus(a,[-b[0],b[1]]);
const times=(a,b)=>rat(a[0]*b[0],a[1]*b[1]);
const over=(a,b)=>rat(a[0]*b[1],a[1]*b[0]);
const dot=(a,b)=>a.reduce((s,x,i)=>plus(s,times(x,b[i])),Q(0));
const trn=A=>A[0].map((_,i)=>A.map(row=>row[i]));
const mm=(A,B)=>A.map(row=>trn(B).map(x=>dot(row,x)));
const op=(A,B,f)=>A.map((a,i)=>a.map((x,j)=>f(x,B[i][j])));
const mv=(A,v)=>A.map(row=>dot(row,v));
const mat=A=>A.map(row=>row.map(Q));
const vec=v=>v.map(Q);
function inv2(A){
  const [[a,b],[c,d]]=A,det=minus(times(a,d),times(b,c));
  return [[d,minus(Q(0),b)],[minus(Q(0),c),a]].map(r=>r.map(x=>over(x,det)));
}
const A=mat([[2,1],[1,3]]),B=mat([[4,1],[1,2]]),M=mat([[1,2],[-1,1]]);
const MT=trn(M),S=op(mm(mm(M,A),MT),B,plus),T=mm(mm(inv2(S),M),A);
const C=op(A,mm(mm(A,MT),T),minus),C2=inv2(op(inv2(A),mm(mm(MT,inv2(B)),M),plus));
ck(C,C2);
for(const i of zz(3))for(const j of zz(3))for(const k of zz(3))for(const l of zz(3)){
  const h=vec([i,j]),z=vec([k,l]),u=mv(MT,z),p=mv(T,h);
  const d=h.map((x,j)=>minus(x,u[j])),v=z.map((x,j)=>minus(x,p[j]));
  ck(plus(dot(d,mv(A,d)),dot(z,mv(B,z))),plus(dot(h,mv(C,h)),dot(v,mv(S,v))));
}
function fixtures(q,a,b,r,d){
  const en=(k,z)=>a*(d*k-r*z)**2+b*d*d*z*z;
  const adm=(k,z)=>k%q!==0||k*r*z>0;
  const pts=[];
  for(const k of zz(2*r+10))for(const z of zz(d+2))if(adm(k,z))pts.push({k,z,e:en(k,z)});
  const E=Math.min(...pts.map(x=>x.e));
  if(q>=2){
    let exp=a*d*d;
    for(let z=1;z<=d;z++)for(let k=1;k<=r+1;k++)exp=Math.min(exp,en(k,z));
    ck(E,exp);
  }
  const cNum=a*b*d*d,cDen=b*d*d+r*r*a;
  tr(E*cDen>=cNum*d*d);
  ck(E*cDen===cNum*d*d, (r*a*d)%cDen===0); // exact resonance of k=1.
  if(d===1&&q>=2)ck(E,Math.min(a,b));
  return {pts,E};
}
for(let q=2;q<=6;q++)for(let a=1;a<=5;a++)for(let b=1;b<=6;b++){
  for(const [r,d] of [[1,1],[2,1],[3,1],[1,2],[2,3],[5,3],[3,5]])
    fixtures(q,a,b,r,d);
}
for(const q of [1,2,3,5]){
  const {E}=fixtures(q,4,1,1,2);ck(E,8);
  ck(fixtures(q,2,3,1,1).E,q===1?3:2);
}
function gcoeff(q,a,b,m,la,k,z){
  const den=sum(zz(50).map(w=>Math.exp(-Math.PI*la*a*(q*w)**2)));
  const num=sum(zz(50).map(w=>Math.exp(-Math.PI*la*(a*(q*w+k-m*z)**2+b*z*z))));
  return num/den;
}
function dcoeff(q,a,b,m,la,k,z){
  const J=Math.ceil(q*Math.sqrt(45*la*a))+10;
  const weights=zz(J).map(w=>Math.exp(-Math.PI*w*w/(q*q*la*a)));
  return Math.exp(-Math.PI*la*b*z*z)*sum(zz(J).map((w,j)=>weights[j]*Math.cos(2*Math.PI*(k-m*z)*w/q)))/sum(weights);
}
for(const q of [1,2,3,5])for(const la of [.5,1,2,5])for(const [a,b,m] of [[1,1,1],[1,2,2/3],[4,1,.5],[2,3,3/2]]){
  for(let k=0;k<q;k++)for(const z of zz(4)){
    const f=gcoeff(q,a,b,m,la,k,z),g=dcoeff(q,a,b,m,la,k,z);
    near(f,g);
    const qhat=k===0?Math.exp(-Math.PI*la*(m*m*a+b)*z*z):0;
    assert(f>=qhat-2e-14);numerical++;
  }
}
// Fourier L1 integration of synthetic discretization/padding law differences,
// after removing the leading exponential analytically for numerical stability.
for(const [q,a,b,r,d] of [[2,1,3,1,1],[3,3,1,2,1],[5,1,1,1,1],[3,4,1,1,2],[2,1,1,2,3]]){
  const {E,pts}=fixtures(q,a,b,r,d),lead=pts.filter(v=>v.e===E);
  const stem=E/(d*d),all=[];
  for(const k of zz(26))for(const z of zz(12))if(k%q!==0||k*r*z>0)
    all.push({k,z,e:(a*(d*k-r*z)**2+b*d*d*z*z)/(d*d)});
  for(const v of all)tr(v.e>=stem);
  const terms=all.filter(v=>v.e<=stem+9);
  const n=513,ph=seq(q).flatMap(j=>seq(n).map(x=>[j/q,x/n]));
  const Lfun=mat=>sum(ph.map(([l,y])=>Math.abs(sum(mat.map(v=>v.w*Math.cos(2*Math.PI*(v.z*y-v.k*l)))))))/(2*ph.length);
  const main=Lfun(lead.map(v=>({...v,w:1})));
  tr(main>0);
  let last=Infinity;
  for(const la of [1,2,4,8]){
    const den=sum(zz(10).map(w=>Math.exp(-Math.PI*la*a*(q*w)**2)));
    const val=Lfun(terms.map(v=>({...v,w:Math.exp(-Math.PI*la*(v.e-stem))/den*
      (v.k%q!==0?1:Math.expm1(-2*Math.PI*la*a*v.k*r*v.z/d)**2)})));
    const err=Math.abs(val-main);
    assert(err<last+2e-12,String([q,a,b,r,d,val,main,last]));last=err;numerical++;
    if(la===8)near(val,main,2e-6);
  }
}
console.log('PASS: '+exact+' exact; '+numerical+' numerical synthetic-noise checks');
