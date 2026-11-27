'use strict';
// Fixed abstract quadratic forms and theta computations.
const A=(x,m)=>{if(!x)throw Error(m);};
let exact=0, numeric=0,maxTheo=0;
const dot=(x,y)=>x[0]*y[0]+x[1]*y[1],mv=(p,x)=>[p[0]*x[0]+p[1]*x[1],p[1]*x[0]+p[2]*x[1]],quad=(p,x)=>dot(x,mv(p,x)),ad=(p)=>[p[2],-p[1],p[0]],add=(x,y)=>x.map((a,i)=>a+y[i]);
const forms=[[1,0,1],[1,1,2],[2,-1,3],[5,2,1],[7,-3,2],[8,1,3]];
for(const P of forms)for(const Q of forms){
 const S=add(P,Q),d=S[0]*S[2]-S[1]**2;
 for(let i=-4;i<=4;i++)for(let j=-4;j<=4;j++)for(const x of [[0,0],[1,-2],[-1,3],[4,3]]){
   let u=[i,j],y=add(x,u),p=mv(P,u),w=add(x.map(v=>v*d),mv(ad(S),p));
   A(d*d*(quad(P,y)+quad(Q,x))===quad(S,w)+d*d*quad(P,u)-d*quad(ad(S),p),'exact matrix completing square');exact++;
 }
}
function sums(P,z){
 let Z=0;
 for(let i=-36;i<=36;i++)for(let j=-36;j<=36;j++)Z+=Math.exp(-quad(P,[i+z[0],j+z[1]]));return Z;
}
const norm=(P,z)=>sums(P,z)/sums(P,[0,0]);
for(const P0 of forms)for(const Q0 of forms)for(const s of [.16,.31,.61,1.2,3.0]){
 const P=P0.map(v=>s*v),Q=Q0.map(v=>s*v*1.21);
 for(const z of [[.13,.22],[.04,.49],[.5,.5],[.34,.09]]){
   A(norm(add(P,Q),z)<=norm(P,z)*norm(Q,z)+1.5e-11,'matrix submultiplicativity');numeric++;
 }
}
function st(t,z){
 let N=Math.ceil(14/Math.sqrt(t))+2,sum=0,d=0,m=t*Math.min(z,1-z)**2;
 for(let i=-N;i<=N;i++){let w=t*(i+z)**2-m,e=Math.exp(-w);sum+=e;d+=w*e;}return [Math.log(sum)-m,Math.log(sum)+d/sum,Math.log(sum)];
}
function ent(t,z,al){
 const a=st(t,z);
 return al===1?a[1]:al===Infinity?a[2]:(st(al*t,z)[0]-al*a[0])/(1-al);
}
function dPhiDirect(a,t){
 const u=Math.PI*Math.PI/t,s=Math.sin(a),c=Math.cos(a);let v=0;
 for(let n=1;n<4000;n++){let x=(2*n-1)*u,e=Math.exp(-x);let v1=2*e*s/(1+2*e*c+e*e);v+=v1;if(v1<1e-16)break;}
 return v/t;
}
function dPhiTrans(a,t){
 let w=t/Math.PI,u=a/Math.PI,ret=u;
 for(let k=1;k<30000;k++){
   let x=w*k,rat=Math.exp(-(Math.PI-a)*x)*(-Math.expm1(-2*a*x))/(-Math.expm1(-2*Math.PI*x));
   ret+=2*(k%2?-1:1)*rat;if(rat<1e-16)break;
 }return ret/(2*Math.PI);
}
const ts=[.2,.37,.61,.91,1.4,2.1,3.5,5.3,8.2,14,22,35,61];
for(const a of [.17,.4,.8,1.4,2,2.7,3.05]){
 let prev=0;
 for(const t of ts){
   let d=dPhiDirect(a,t),v=dPhiTrans(a,t);
   A(Math.abs(d-v)<4e-14,'two Poisson sides');A(d>=prev-1e-15,'theta mixture monotonic');numeric+=2;maxTheo=Math.max(maxTheo,Math.abs(d-v));prev=d;
 }
}
for(const t of ts)for(const al of [.15,.43,.8,.97,1,1.05,1.25,2,3.6,8,Infinity]){
 let hp=ent(t,0,al);
 for(let j=1;j<=50;j++){
   const h=ent(t,j/100,al);
   A(h>=hp-9e-12,'all orders toward half-shift');numeric++;
   hp=h;
 }
}
for(const t of [.15,.21,.3,.41]){
 let f0=st(t,0)[0],f1=st(t,.5)[0];
 A((1+Math.exp(-t))*Math.exp(-f0)<2*Math.exp(-t/4-f1),'not majorized in top two');A(Math.exp(-f0)>Math.exp(-t/4-f1),'top atom ordering');numeric+=2;
}
console.log(JSON.stringify({exact,numeric,maxThetaIdentityError:maxTheo}));
