'use strict';
// Direct checks on synthetic one- and two-dimensional Gaussian masses and moments.
const assert=(b,m)=>{if(!b)throw Error(m);};
const range=n=>Array.from({length:2*n+1},(_,i)=>i-n);
function moment(D,Q,H,z,lo,lp){const d=z.length;let out=[0,0];const M=50; const r1=range(M),r2=d===1?[0]:r1;
 for(let i of r1)for(let j of r2){
   let x=D[0]*i+(d===2?D[1]*j:0)+z[0],y=d===2?D[2]*j+z[1]:0;
   let b=Q[0]*x*x+(d===2?2*Q[1]*x*y+Q[2]*y*y:0);
   let q=H[0]*x*x+(d===2?2*H[1]*x*y+H[2]*y*y:0);
   let w=Math.exp(-b);
   out[0]+=w;out[1]+=lo===0?Math.max(0,q)**(lp/2)*w:w*Math.exp(-lo*q);
 }return [out[0],out[1]/out[0]];
}
let num=0,exact=0;
for(let n=1;n<=25;n++){
  let d=2*n,j=n,a2=d*d,b2=6*j*j-6*d*j+d*d;
  assert(2*(b2-a2)===-3*d*d,'exact Bernoulli difference');exact++;
}
for(let C of [[1,0,1],[1,.31,1],[.6,.85,1.37]])for(let Q of [[.41,.03,.27],[.83,-.39,.74],[1.17,.28,1.65]])for(let H of [[1,0,1],[.8,.42,1.3],[1,.4,.16]])for(let z of [[.03,.49],[.18,.22],[.38,.63],[.5,.5]]){
 for(let p of [.25,.5,1,1.5,2]){
    let [_,v]=moment(C,Q,H,z,0,p),[__,b]=moment(C,Q,H,[0,0],0,p);
    assert(v>=b-3e-12,'fractional-power order '+JSON.stringify({C,Q,H,z,p,v,b}));num++;
 }
 for(let t of [.1,.3,1,3]){
    let [_,v]=moment(C,Q,H,z,t,0),[__,b]=moment(C,Q,H,[0,0],t,0);
    assert(v<=b+3e-12,'Laplace order');num++;
 }
}
function gamma(z){
 const c=[676.5203681218851,-1259.1392167224028,771.3234287776531,-176.6150291621406,12.507343278686905,-.13857109526572012,9.984369578019572e-6,1.5056327351493116e-7];
 if(z<.5)return Math.PI/Math.sin(Math.PI*z)/gamma(1-z);
 z-=1;let x=.99999999999980993;
 for(let i=0;i<c.length;i++)x+=c[i]/(z+i+1);
 let y=z+c.length-.5;
 return Math.sqrt(2*Math.PI)*y**(z+.5)*Math.exp(-y)*x;
}
function basic(p,s,z,r=-1){
  let num=0,den=0;
  for(let i of range(Math.ceil(14*s))){
    let x=Math.abs(i+z),w=Math.exp(-((x/s)**2));
    num+=(r<0?x**p:Math.max(0,x-r))*w;den+=w;
  }return num/den;
}
let maxPow=0,maxHinge=0;
for(let p of [2.12,2.3,2.6,2.9,3,3.1,3.4,3.7,3.9]){
 const c=-2*gamma(p+1)*Math.sin(p*Math.PI/2)/(2*Math.PI)**(p+1);
 let v=0;for(let i=1;i<10000;i+=2)v+=i**(-p-1);
 const lead=4*c*v/Math.sqrt(Math.PI);
 for(let s of [4,7,10,16]){
    let x=s*(basic(p,s,0)-basic(p,s,.5));
    const rel=Math.abs(x/lead-1);assert(rel<.10,'wide fractional-power coefficient');num++;
    maxPow=Math.max(maxPow,rel);
 }
}
for(let s of [3,5,8,13,21,34,55]){
 let x=s*(basic(1,s,0,.5)-basic(1,s,.5,.5)),lead=1/(4*Math.sqrt(Math.PI));
 let error=Math.abs(x/lead-1); assert(error<.1,'hinge counterexample coefficient');num++;maxHinge=Math.max(maxHinge,error);
}
for(let s of [1.05,1.20,1.35,1.48,1.61]){
 let x=basic(4,s,0)-basic(4,s,.5);
 let lead=4*s**4*(Math.PI**4*s**4-3*Math.PI**2*s**2)*Math.exp(-(Math.PI**2*s**2));
 assert(x>0&&Math.abs(x/lead-1)<.001,'fourth power reverses');num++;
}
let maxCusp=0;
for(let Q of [.9,1.2,2,2.7])for(let p of [.3,.55,1,1.2,1.6]){
 let [Z,b]=moment([1],[Q],[1],[0],0,p);
 for(let z of [.003,.001,.0001]){
  let [_b,v]=moment([1],[Q],[1],[z],0,p);
  let e=Math.abs((v-b)/(z**p/Z)-1);assert(e<.1,'exact first local cusp');num++;maxCusp=Math.max(maxCusp,e);
 }
}
console.log(JSON.stringify({num,exact,maxPow,maxHinge,maxCusp}));
