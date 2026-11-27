// Run: node verify_factor_stewart_exact_threshold.js
"use strict";
function verify() {
  let checks=0, internal=0;
  const ok=(x,msg)=>{++checks;if(!x)throw Error(msg);};
  function isqrt(x){
    if(x<2n)return x;
    let y=1n<<BigInt(Math.ceil(x.toString(2).length/2));
    for(;;){const z=(y+x/y)/2n;if(z>=y)return y;y=z;}
  }
  const cases=[[-1n,1n],[0n,1n],[1n,3n],[2n,1n],[7n,2n],[4n,1n]];
  for(let n=1n;n<=20000n;n++){
    const u=n**5n,V=3125n*u*u-125n*u+1n,C=V**3n,F=(125n*n**6n-3n*n)**5n,G=F-C;
    ok(G===78125n*u**3n-5625n*u*u+132n*u-1n&&G>0n,"positive gap polynomial");
    ok(4n*V+1n===5n*(50n*u-1n)**2n,"square identity");
    const B=50n*G+15n*V;
    ok(B+3n===(25n*V+7n)*(50n*u-1n),"gap-length identity");
    const A=(200n*V+81n)**2n*V;
    ok(A<80n*(B+3n)**2n,"constant correction -3/50 fails strictly");
    ok(A>80n*B**2n,"constant correction 0 spans the pair strictly");
    const x=isqrt(F);
    ok(x*x<=F&&F<(x+1n)**2n,"floor square");
    if(C<x*x&&x*x<F)++internal;
    for(const [a,d] of cases){
      let count=0;
      for(let k=0n;k<=6n;k++){
        const s=a-k*d;
        if(s>0n){
          // By the printed derivative bound, G-L_*(C-k) < k/sqrt(C-k).
          ok(k*k*d*d<(C-k)*s*s,"strict fixed-slack start certificate");
          count++;
        } else if(k===0n&&a===0n)count++;
      }
      const expected=a<0n?0:a===0n?1:Number((a+d-1n)/d);
      ok(count===expected,"constant-scale start multiplicity");
    }
  }
  return {checks,parameters:20000,strictlyInternalSquares:internal};
}
console.log(JSON.stringify(verify()));
