// Run: node verify_factor_singmaster_projection.js
// Finite exact checks of the algebra behind the shifted-contour estimate.
"use strict";
function verify() {
  let checks = 0;
  function ok(a, msg) { ++checks; if (!a) throw Error(msg); }
  const pow = (a,n) => a ** BigInt(n);
  const abs = x => x < 0n ? -x : x;
  const fi = [1n];
  for (let k=1;k<=120;k++) fi.push(fi[k-1]*BigInt(k));
  const mul = ([a,b],[c,d]) => [a*c-b*d,a*d+b*c];
  const norm2 = ([a,b]) => a*a+b*b;
  // For z Gaussian integral, returns 2^d times P(z/2).
  function scaled(a,z) {
    let v=[0n,0n], q=1n;
    for(let i=a.length-1;i>=0;i--) {
      v=mul(v,z); v[0]+=q*a[i]; q*=2n;
    }
    return v;
  }
  const evalInt=(a,w)=>a.reduceRight((x,ci)=>w*x+ci,0n);
  function test(k,T,m,salt) {
    const nu=m.reduce((a,b)=>a+b,0), U=16n*BigInt(k+1)*T;
    let a=[1n];
    for(let j=0;j<=k;j++) {
      const b=BigInt(j)*T;
      for(let i=0;i<m[j];i++){
        const next=Array(a.length+1).fill(0n);
        for(let l=0;l<a.length;l++) {next[l]-=b*a[l];next[l+1]+=a[l];}
        a=next;
      }
    }
    const tails=Array.from({length:nu},(_,i)=>a.slice(i+1));
    const majorant=a.reduce((v,ai,i)=>v+abs(ai)*pow(U,i),0n);
    ok(majorant===m.reduce((acc,mi,j)=>acc*pow(U+BigInt(j)*T,mi),1n),"coefficient majorant");
    ok(U>=2n*BigInt(nu),"factorial scale");
    for(let j=0;j<=k;j++){
      const b=2n*BigInt(j)*T;
      for(const z of [[b+T,0n],[b-T,0n],[b,T],[b,-T]]){
        ok(norm2(z)<=4n*U*U,"outer radius");
        for(let h=0;h<=k;h++) {
          const a0=T*BigInt(Math.max(1,Math.abs(h-j)));
          ok(norm2([z[0]-2n*BigInt(h)*T,z[1]])>=a0*a0,"pole separation");
        }
        for(let i=0;i<nu;i++){
          const d=nu-i-1;
          ok(pow(U,2*(i+1))*norm2(scaled(tails[i],z)) <= pow(2n,2*d)*majorant**2n,"tail bound");
        }
      }
    }
    const r=m.map((mi,j)=>Array.from({length:mi},(_,p)=>BigInt((p*p+11*p+13*j+(p+7*j)*salt+salt*salt)%23-11)));
    const y=Array.from({length:nu},(_,i)=>r.reduce((v,rs,j)=>
      v+rs.reduce((s,b,p)=>p>i?s:s+b*(fi[i]/fi[i-p])*pow(BigInt(j)*T,i-p),0n),0n));
    for (const w of [-T-1n,-1n,BigInt(k+1)*T+1n,BigInt(k+2)*T+3n]) {
      const chi=evalInt(a,w);
      const lhs=tails.reduce((acc,t,i)=>acc+y[i]*evalInt(t,w),0n);
      let rhs=0n;
      for(let j=0;j<=k;j++) for(let p=0;p<m[j];p++) {
        const den=pow(w-BigInt(j)*T,p+1);
        ok(chi%den===0n,"exact division by pole powers");
        rhs+=r[j][p]*fi[p]*(chi/den);
      }
      ok(lhs===rhs,"Laplace numerator identity");
    }
  }
  for(let k=1;k<=8;k++) for(let t=1;t<=8;t++) for(let salt=0;salt<15;salt++) {
    const m=Array.from({length:k+1},(_,j)=>1+(salt*salt+3*salt*j+7*j*j+11*t)%5);
    test(k,BigInt(t),m,salt);
  }
  for(let k=1;k<=120;k++){
    ok(fi[k]*pow(3n,k)>=pow(BigInt(k),k),"elementary factorial lower bound");
    for(let j=0;j<=k;j++){
      const q=fi[j]*fi[k-j];
      ok(fi[k]%q===0n,"binomial integrality");
      ok(q*pow(2n,k)>=fi[k],"factorial product lower bound");
    }
  }
  return {checks};
}
console.log(JSON.stringify(verify()));
