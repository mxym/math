'use strict';
// Fixed mathematical examples only. No cryptographic instance or external input.
let exact=0,numeric=0;
function check(ok,label){if(!ok)throw Error(label);exact++;}
function near(x,y,e,label){if(!Number.isFinite(x)||!Number.isFinite(y)||Math.abs(x-y)>e)throw Error(label+': '+x+' vs '+y);numeric++;}
function le(x,y,e,label){if(!Number.isFinite(x)||!Number.isFinite(y)||x>y+e)throw Error(label+': '+x+' > '+y);numeric++;}
const seq=n=>Array.from({length:n},(_,i)=>i);
const sum=a=>a.reduce((x,y)=>x+y,0);
let state=0x34b0ad77;
function gen(k){state=(Math.imul(state,1664525)+1013904223)>>>0;return (state>>>8)%k;}
const mod4=j=>((j%4)+4)%4;
const reI=j=>[1n,0n,-1n,0n][mod4(j)];

// The phase-pairing cancellation giving a rank-one complex zero.
for(let j=-600;j<=600;j++){
  const k=-j-1;
  check(j*j+j===k*k+k,'pair exponent at the candidate zero');
  check((j&1)!==(k&1),'pair sign at the candidate zero');
}
for(let j=2;j<=120;j++)check(BigInt(j)<=2n**BigInt(j-1),'logarithmic series geometric majorant');
const phase=[[65n,0n],[39n,52n],[25n,60n],[0n,65n],[-39n,52n],[-65n,0n],[-25n,-60n],[0n,-65n]];
for(let rep=0;rep<2400;rep++){
  const M=2+gen(8);
  let n=0n,S=0n,A=0n,B=0n,U=0n,C=0n,D=0n;
  const sample=[];
  for(let j=0;j<M;j++){
    const w=BigInt(1+gen(11)),t=BigInt(gen(10)),[x,y]=phase[gen(phase.length)];
    n+=w;S+=w*t*t;A+=w*t*t*x*x;B+=w*t*t*y*y;
    U+=w*t*t*y;C+=w*t*x;D+=w*t*y;
    sample.push([w,t]);
  }
  check(A+B===65n*65n*S,'odd phase squared identity');
  check(U*U<=S*B,'odd phase first-term Cauchy Schwarz');
  check(C*C<=n*A,'odd phase real Cauchy Schwarz');
  check(D*D<=n*B,'odd phase imaginary Cauchy Schwarz');
  const p=BigInt(2+gen(8)),ws=sample.map(([w,t])=>w+t);
  const all=ws.reduce((a,b)=>a+b,0n),pw=ws.reduce((a,b)=>a+b**p,0n);
  check(pw<=all**p,'paired width inflation inequality');
}

// Exact differentiation of a short cosine product versus signed Fourier convolution.
for(let rep=0;rep<320;rep++){
  const atoms=Array.from({length:3+gen(4)},()=>[1+gen(9),gen(4),1+gen(7)]);
  const k=1+gen(21);
  let cosine=0n,conv=0n;
  for(const [f,p,a] of atoms)for(const [g,q,b] of atoms){
    const power=x=>BigInt(x)**BigInt(k);
    cosine+=2n*BigInt(a*b)*(reI(p+q+k)*power(f+g)+reI(p-q+k)*power(f-g));
    for(const u of [-1,1])for(const v of [-1,1])
      conv+=BigInt(a*b)*reI(u*p+v*q+k)*power(u*f+v*g);
  }
  check(cosine===conv,'paired cosine power rule');
}

// Convex support line: use stable log-cosh to cover a growing-order mesh.
const lc=x=>Math.abs(x)+Math.log1p(Math.exp(-2*Math.abs(x)))-Math.log(2);
for(const ell of [17,21,28,50,90,150,260,370]){
  const eps=2*Math.exp(-ell),H=2*ell+Math.log1p(eps/2);
  for(let p=1;p<=Math.floor(1.79*ell);p++){
    const K=H*Math.tanh(H)/p, a=Math.pow(p/H,p);
    le(1+K*(a-1),0,1e-14,'tangent below zero before convex portion');
    for(const r of [.0,.25,.5,.82,.93,.97,.997,.9999,1,1.0001,1.003,1.03,1.1,1.6,2]){
      const l=1+K*(Math.pow(r,p)-1);
      if(l>0)le(Math.log(l),lc(r*H)-lc(H),2e-12,'global cosh supporting line');
    }
  }
}
for(const c of [0,.08,.24,.45,.68,.9,1]){
  const phi=x=>Math.cosh(c*Math.acosh(x));
  for(let j=0;j<220;j++){
    const x=1+gen(1000)/13,y=1+gen(800)/17,p=gen(100)/100;
    le(p*phi(x)+(1-p)*phi(y),phi(p*x+(1-p)*y),1e-11,'concave fractional cosh');
  }
}

// Exact rank-one log-Fourier coefficients are obtained from the Jacobi product.
// Evaluate their rapidly convergent finite approximation and check the parity window.
function qAt(eps){
  let a=0,b=eps/2;
  for(let iter=0;iter<70;iter++){
    const q=(a+b)/2;
    let m=0; for(let j=1;j<=9;j++)m+=2*Math.pow(q,j*j);
    if(m<eps)a=q;else b=q;
  }
  return (a+b)/2;
}
function logCoefs(eps,k){
  const q=qAt(eps),ell=Math.log(2/eps),g2=-2*Math.log(q);
  const gr=Math.exp((k/2)*Math.log(g2/(2*ell)));
  return seq(35).map(i=>{
    const j=i+1,sgn=j&1?1:-1;
    return gr*2*sgn*Math.exp(j*Math.log(q)+(k-1)*Math.log(j)-Math.log(eps))/(1-Math.pow(q,2*j));
  });
}
function trig(phase,k){
  return [Math.cos(phase),-Math.sin(phase),-Math.cos(phase),Math.sin(phase)][mod4(k)];
}
for(const k of [20,21,29,38,47,58,69,90,103,140,165]){
  for(const d of [.13,.45,1.1,2.2]){
    const eps=4*d*Math.pow(2,-k), v=logCoefs(eps,k);
    const a=k&1?4*d/(1+Math.sqrt(1+32*d*d)):1;
    const theta=k&1?Math.acos(-a):Math.PI;
    const expected=k&1?Math.sqrt(1-a*a)*(1+2*d*a):1+d;
    const val=t=>Math.abs(sum(v.map((c,i)=>c*trig((i+1)*t,k))));
    const tail=sum(v.slice(2).map(Math.abs))+Math.abs(v[0]-1)+Math.abs(v[1]+d);
    near(val(theta),expected,tail+1e-11,'rank-one critical witness');
    for(let j=0;j<=25;j++)le(val(2*Math.PI*gen(1000)/1000),expected+tail,1e-11,'parity supremum on phase grid');
    if(k>=58)near(val(theta),expected,2e-5,'critical convergence');
  }
}
for(const k of [1,2,3,6,9,15,20,33]){
  const eps=Math.exp(-3*k-20),v=logCoefs(eps,k);
  const theta=k&1?Math.PI/2:0;
  near(Math.abs(sum(v.map((c,i)=>c*trig((i+1)*theta,k)))),1,3e-9,'subcritical scale');
}

// Nonrectangular finite theta sums check the real modulus and complex tube majorant.
function norm2(u){return u[0]*u[0]+u[1]*u[1];}
for(const g of [3.6,4.35,5.4,6.7,8.7]){
  for(const B of [[1,.15,0,1.2],[1,-.42,.1,1.4],[1,.48,.2,1.35]]){
    const reps=[];
    for(let i=-7;i<=7;i++)for(let j=-7;j<=7;j++){
      if(i<0||(i===0&&j<=0))continue;
      const b=[g*(B[0]*i+B[1]*j),g*(B[2]*i+B[3]*j)];
      reps.push([b,2*Math.exp(-norm2(b)/2)]);
    }
    const eps=sum(reps.map(([b,w])=>w))*1.000000001;
    const ell=Math.log(2/eps),R=Math.sqrt(2*ell),H=2*ell+Math.log1p(eps/2),Rp=H/R;
    for(let iter=0;iter<95;iter++){
      const ang=2*Math.PI*gen(10000)/10000;
      const u=[Math.cos(ang),Math.sin(ang)],z=[gen(500)/37,gen(500)/37];
      const r=gen(500)/R/100,s=R*gen(900)/1000;
      const dot=(x,y)=>x[0]*y[0]+x[1]*y[1];
      let h0=0,h1=0,re=0,im=0;
      for(const [b,w] of reps){
        const th=dot(b,z),v=dot(b,u);
        h0+=w*Math.cos(th);h1+=w*Math.cos(th+r*v);
        const a=Math.exp(-norm2(b)/2+s*v),c=Math.exp(-norm2(b)/2-s*v);
        re+=Math.cos(th)*(a+c);im-=Math.sin(th)*(a-c);
      }
      le(Math.abs(Math.log1p(h1)-Math.log1p(h0))/eps,2*Math.sin(Math.min(Math.PI,r*Rp)/2)/(1-eps),5e-10,'real displacement profile');
      le(Math.hypot(re,im)/(eps*Math.cosh(s*Rp)),1,5e-10,'complex envelope');
    }
  }
}
for(const eps of [.1,.2,.35]){
  const n=Math.exp(220),p=Math.expm1(Math.log1p(eps)/n),q=qAt(p);
  const g2=-2*Math.log(q),trace=2*n*q*g2/(1+p);
  near(trace/(2*Math.log1p(eps)*Math.log(n)),1,.016,'trace can grow while norm shrinks');
}
console.log({exact_checks:exact,numerical_checks:numeric});
