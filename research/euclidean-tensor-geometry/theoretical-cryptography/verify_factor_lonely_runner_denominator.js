// Run: node verify_factor_lonely_runner_denominator.js
// Verify exact modular certificates and the explicit rational witness in finite cases.
"use strict";
function verify() {
  const gcd=(a,b)=>{while(b){[a,b]=[b,a%b];}return a;};
  const residue=(x,d)=>((x%d)+d)%d;
  let checks=0, classes=0;
  const ok=(why,x)=>{++checks;if(!x)throw Error(why);};
  function scan(h) {
    const n=360*h+4,m=10*h,ell=6*h+1,C=120*h-4,c0=60*h+2,Q=30*h-5;
    const bound=2*n+2*ell+1;
    const lows=new Set(Array.from({length:ell},(_,i)=>i+1));
    for(let k=1;k<=5*h-1;k++)lows.add(6*k);
    const holes=new Set(Array.from({length:m},(_,i)=>n+c0+6*i));
    const V=new Set([...lows]);
    for(let v=n+1;v<=2*n;v++)if(!holes.has(v))V.add(v);
    ok("speed count and primitive",V.size===n&&V.has(1)&&V.has(2*n));
    for(let d=1;d<=n+1;d++) {
      const v=d<=n-C?Math.ceil((n+C+1)/d)*d:d<=n?2*d:d;
      ok("small denominator multiple",V.has(v)&&v%d===0);
    }
    const rdist=(v,x,d)=>{
      // Here x is a unit, representing the inverse numerator modulo d.
      const r=residue(v,d);
      if(!r)return 0;
      if(r===x||r===d-x)return 1;
      const s=2*x%d;
      if(r===s||r===d-s)return 2;
      return Infinity;
    };
    for(let d=n+2;d<=bound;d++) {
      if(V.has(d)){ok("selected denominator",d<=2*n);continue;}
      for(let x=1;2*x<=d;x++)if(gcd(x,d)===1){
        ++classes;
        let v;
        if(d<=2*n) {
          ok("omitted denominator is a hole",holes.has(d));
          v=V.has(d+x)?d+x:V.has(d-x)?d-x:x;
        } else {
          const j=d-2*n;
          if(j<=2)v=x===1?1:d-x;
          else if(x<j)v=x<=ell?x:d-2*x;
          else v=V.has(d-x)?d-x:2*x;
        }
        const r=rdist(v,x,d);
        ok("blocked reduced numerator",V.has(v)&&(n+1)*r<d);
      }
    }
    const den=3*n*Q, num=3*n+1;
    let dmin=den;
    for(const v of V){
      const z=(v*num)%den,r=Math.min(z,den-z);
      dmin=Math.min(dmin,r);
      ok("explicit witness margin",3*Q*r>=den);
      ok("more than four times the conjectured threshold",(n+1)*r>4*den);
    }
    return {h,n,bound,minAtExplicitTime:[dmin,den]};
  }
  const samples=Array.from({length:8},(_,i)=>scan(i+1));
  function small(n) {
    const V=[1,...Array.from({length:n},(_,i)=>n+1+i).filter(v=>v!==n+2)];
    let least=null;
    for(let d=1;d<=2*n+5;d++)for(let a=0;2*a<=d;a++)if(gcd(a,d)===1) {
      if(V.every(v=>{const r=(a*v)%d;return (n+1)*Math.min(r,d-r)>=d;})&&least===null)least=d;
    }
    ok("exact denominator of one-hole family",least===2*n+5);
  }
  for(let n=10;n<=130;n+=6)small(n);
  return {checks,classes,samples};
}
console.log(JSON.stringify(verify(),null,2));
