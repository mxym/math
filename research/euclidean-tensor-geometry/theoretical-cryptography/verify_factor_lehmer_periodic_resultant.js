// Run: node verify_factor_lehmer_periodic_resultant.js
"use strict";
function verify() {
  let checks=0, nonzero=0;
  const ok=(a,m)=>{++checks;if(!a)throw Error(m);};
  function det(A){
    const n=A.length;let sign=1n,prev=1n;
    for(let j=0;j+1<n;j++){
      let k=j;while(k<n&&A[k][j]===0n)k++;
      if(k===n)return 0n;
      if(k!==j){[A[j],A[k]]=[A[k],A[j]];sign=-sign;}
      const pivot=A[j][j];
      for(let i=j+1;i<n;i++){
        for(let l=j+1;l<n;l++){
          const r=pivot*A[i][l]-A[i][j]*A[j][l];
          ok(r%prev===0n,"Bareiss division");
          A[i][l]=r/prev;
        }
        A[i][j]=0n;
      }
      prev=pivot;
    }
    return sign*A[n-1][n-1];
  }
  function resCycle(p,N){
    const d=p.length-1;
    function xTimes(a){
      const z=a[d-1];
      return Array.from({length:d},(_,j)=>(j?a[j-1]:0n)-z*p[j]);
    }
    let a=Array(d).fill(0n);a[0]=1n;
    for(let j=0;j<N;j++)a=xTimes(a);a[0]-=1n;
    const M=Array.from({length:d},()=>Array(d));
    for(let j=0;j<d;j++){
      for(let i=0;i<d;i++)M[i][j]=a[i];
      a=xTimes(a);
    }
    return det(M);
  }
  const abs=x=>x<0n?-x:x;
  for (const d of [2,4,6,8,10,12,14,16]) for(const m of [2n,3n,4n,5n,6n,7n,8n]){
    for(const a of [-1n,0n,1n,2n,4n])for(let salt=0;salt<4;salt++){
      const P=Array(d+1).fill(0n); P[0]=1n;P[d]=1n;
      for(let j=1;j<d;j++)P[j]=(j%2?a:2n)+m*BigInt((j*j*13+salt*7+j*31)%11-5);
      if(salt%2)for(let j=1;j<d/2;j++)P[d-j]=P[j];
      let plain=resCycle(P,d);
      if(plain!==0n)nonzero++;
      const h=BigInt(d-2);
      ok(plain%(m**h)===0n,"periodic resultant divisibility");
      if(m===5n&&d%10===0&&a===-1n)ok(plain%(5n**BigInt(d))===0n,"endpoint resultant bonus");
      for(const [p,t] of [[2,2],[3,1],[5,1],[7,1]]){
        if(m%BigInt(p)!==0n)continue;
        const r=resCycle(P,d*p**t);
        ok(r%(m**h*BigInt(p)**(h*BigInt(t)))===0n,"p-power amplifier divisibility");
      }
    }
  }
  for(let n=1;n<=10;n++)for(let s=1;s<=25;s++){
    let A=1n,B=1n,P=1n;
    for(let j=1;j<=n;j++){
      const b=BigInt((s*s+3*j)%37+1), a=b+BigInt((s*j*13)%71);
      A*=a;B*=b;P*=a+b;
    }
    ok(P<=2n**BigInt(n-1)*(A+B),"reciprocal pair cosh product");
  }
  ok(4n*(9n**6n+5n**6n)<25n*9n**3n*5n**3n,"uniform mod-5 bound >9/5");
  ok(4n*(2n**6n+1n)>25n*2n**3n,"uniform mod-5 bound <2");
  // Monotone starting cases for the common bound 4/3.
  for(const [B,Nmult,D] of [[4n,1n,6n],[9n,3n,6n],[8n,4n,12n]]){
    const k=Nmult*D,A=4n**k,b=3n**k;
    ok(2n*4n**Nmult<B*3n**Nmult,"decreasing exponential ratio");
    ok(2n**(D-2n)*(A+b)**2n<B**(D-2n)*A*b,"strict bound at starting degree");
  }
  return {checks,nonzeroSyntheticResultants:nonzero};
}
console.log(JSON.stringify(verify()));
