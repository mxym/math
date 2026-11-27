"use strict";
let exact=0,numeric=0;
function check(ok,msg,fp=false){
  if(!ok)throw Error(msg);
  if(fp)++numeric;else ++exact;
}
const mod=(a,n)=>(a%n+n)%n;
for(let b=1;b<=9;++b)for(let a=1;a<=18;++a)
for(let bt=-7;bt<=7;++bt)for(let gt=-7;gt<=7;++gt){
  let subset=true;
  for(let j=-6;j<=6;++j){
    const v=a*(2*j+1)-bt;
    if(mod(v+gt-b,2*b)!==0)subset=false;
  }
  check(subset===(a%b===0 && mod(a+gt-bt-b,2*b)===0),"zero-spacing equivalence");
}
for(let p=3;p<=11;p+=2){
  let min=null,count=0;
  for(let m=1;m<(1<<p)-1;++m){
    let k=0;
    for(let q=m;q;q&=q-1)++k;
    const n=k*(p-k);
    if(min===null||n<min){min=n;count=1;}
    else if(n===min)++count;
  }
  check(min===p-1&&count===2*p,"projected shortest binary-shell count");
}
for(let B=1n;B<=10n;++B)for(let A=1n;A<=13n;++A)
for(let c=1n;c<=7n;++c)for(let d=1n;d<=5n;++d){
  // For q=A/B and z=c/d, check L_{q,+}(z)=z L_{1/q,-}(z)
  // by cross multiplication only (all denominators positive).
  const lhsNum=B*d+A*c, lhsDen=(A+B)*d;
  const rhsNum=c*(A*c+B*d), rhsDen=d*(A+B)*c;
  check(lhsNum*rhsDen===rhsNum*lhsDen,"Bernoulli orientation monomial");
}
function LSE(a,b,w){
  let terms=[];
  for(let x=-100;x<=100;++x)terms.push(-a*x*x+(b+w)*x);
  const M=Math.max(...terms);
  return M+Math.log(terms.reduce((q,r)=>q+Math.exp(r-M),0));
}
const lp=x=>x>0?x+Math.log1p(Math.exp(-x)):Math.log1p(Math.exp(x));
for(const b of [1,2,3,5])for(const L of [1,2,3,4,7])
for(const bt of [-31,-13,0,2,17,37])for(const shift of [-6,0,5]){
  const gt=bt+b*(1-L+2*shift), a=L*b;
  for(const w of [-.65,.24,1.1]){
    const B=b/4,A=a/4, G=gt/4,H=bt/4;
    const target=LSE(B,G,w)-LSE(B,G,0);
    const source=LSE(A,H,w)-LSE(A,H,0);
    let right=0;
    for(const sign of [-1,1])for(let r=1;r<=100;++r){
      const zero=sign*b*(2*r-1)-gt;
      if(mod(zero+bt-a,2*a)===0){
        const sourceSign=Math.sign(zero+bt);
        check(sourceSign!==0,"matched zero has orientation");
        right+=(sign-sourceSign)/2*w;
      }else{
        const z=-sign*zero/4;
        right+=lp(z+sign*w)-lp(z);
      }
    }
    check(Math.abs(target-source-right)<2e-10,"theta quotient against retained positive factors",true);
  }
}

function tr(A){return A[0].map((_,i)=>A.map(r=>r[i]));}
function mm(A,B){return A.map(row=>B[0].map((_,j)=>row.reduce((s,x,i)=>s+x*B[i][j],0)));}
for(let s=-4;s<=4;++s)for(let t=-4;t<=4;++t)for(let u=-4;u<=4;++u){
  const Q=[[1,s,t],[0,1,u],[0,0,1]],
        R=[[1,-s,s*u-t],[0,1,-u],[0,0,1]],
        D=[[7,0,0],[0,5,2],[0,2,6]],
        B=mm(mm(Q,D),tr(Q));
  const E=mm(mm(R,B),tr(R)), X=mm(R,Q);
  for(let i=0;i<3;++i)for(let j=0;j<3;++j){
    check(E[i][j]===D[i][j],"precision congruence");
    check(X[i][j]===+(i===j),"real-imaginary basis pairing");
  }
}
console.log("Lattice Gaussian additive factor checks: "+exact+" exact and "+numeric+" floating comparisons passed.");
