'use strict';
// Pure moment/periodization checks on Gaussian toy distributions; no secret samples.
let checks=0;
function df(j){let ans=1n;for(let k=j;k>0;k-=2)ans*=BigInt(k);return ans;}
const moment=j=>j%2?0n:j===0?1n:df(j-1);
function ip(a,b){let z=0n;a.forEach((x,i)=>b.forEach((y,j)=>z+=BigInt(x)*BigInt(y)*moment(i+j)));return z;}
function eq(x,y){checks++;if(x!==y)throw Error(x+' != '+y);}
const H=[-3,0,6,0,-1],M=[0,1],S=[-1,0,1];
eq(ip(H,[1]),0n);eq(ip(H,H),24n);eq(ip(H,M),0n);eq(ip(H,S),0n);
eq(ip(M,M),1n);eq(ip(S,S),2n);eq(ip(M,S),0n);
for(let a=-3;a<=3;a++)for(let s=-3;s<=3;s++){
 const h=H.map((v,i)=>v+2880*a*(M[i]||0)+1440*s*(S[i]||0));
 eq(ip(h,h),24n+2880n**2n*BigInt(a*a)+2n*1440n**2n*BigInt(s*s));
}
// On a Fourier axis, any quadratic symbol matching k^4 at k=1 misses by 12 at k=2.
eq(2n**4n-2n**2n,12n);
const quadrature=[];
for(const alpha of [2,3,6]){
 const n=2048,rows=[];let h2=0,s2=0,hs=0;
 for(let i=0;i<n;i++){
  const x=alpha*(i+.5)/n-alpha/2;
  let density=0,hn=0,sn=0;
  for(let j=-10;j<=10;j++){
   const z=x+alpha*j,w=Math.exp(-z*z/2)/Math.sqrt(2*Math.PI);
   density+=w;hn+=w*(-(z**4)+6*z*z-3)/2880;sn+=w*(z*z-1)/2;
  }
  const h=hn/density,s=sn/density,p=density*alpha/n;
  h2+=p*h*h;s2+=p*s*s;hs+=p*h*s;rows.push([p,h,s]);
 }
 const shift=-hs/s2;
 const residual=rows.reduce((a,[p,h,s])=>a+p*(h+shift*s)**2,0);
 if(!(residual>0&&residual<h2))throw Error('toy projected residual');
 if(Math.abs(residual-(h2-hs*hs/s2))>1e-17)throw Error('orthogonal check');
 quadrature.push({alpha,unretuned:h2,optimalVariancePerturbation:shift,residual});
}
console.log({exactMomentChecks:checks,wrappedQuadrature:quadrature});