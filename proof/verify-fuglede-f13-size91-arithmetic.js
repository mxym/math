'use strict';
const p=13,m=7,C=21,mod=x=>(x%p+p)%p;
const inv=Array(p).fill(0);
for(let a=1;a<p;a++)for(let b=1;b<p;b++)if(a*b%p===1)inv[a]=b;
const assert=(a,msg)=>{if(!a)throw Error(msg);};
const patterns=Array.from({length:p},()=>[]);
let allQuadraticCount=0;
for(let a=1;a<p;a++)for(let c=0;c<p;c++){
  // A genuine quadratic reduces by translating its argument to c+a t^2.
  const vals=Array.from({length:p},(_,t)=>mod(c+a*t*t));
  const lift=(m*p-vals.reduce((s,n)=>s+n,0))/p;
  if(!Number.isInteger(lift)||lift<0||lift>vals.filter(x=>x===0).length)continue;
  const k=(vals.reduce((s,n)=>s+n*(n-1)/2,0)+lift*p*(p-1)/2-p*m*(m-1)/2)/p;
  assert(Number.isInteger(k)&&k>=4,"small or nonintegral quadratic weight");
  ++allQuadraticCount;
  if(lift===0)patterns[a].push({c,k});
}
assert(allQuadraticCount===96,"quadratic count");
console.log({allQuadraticCount});

function tightPencils(L){
  let masks=0, leading=0, weights=0, constants=0;
  function mask(s,t=0){
    ++masks;
    // forms x,y,x+y,x+s*y[,x+t*y]
    for(let a3=1;a3<p;a3++)for(let a4=(L===5?1:0);a4<(L===5?p:1);a4++){
      const a2=mod(-a3*s-a4*t);
      const a0=mod(-a2-a3-a4),a1=mod(-a2-a3*s*s-a4*t*t);
      if(!a0||!a1||!a2)continue;
      const a=[a0,a1,a2,a3,...(L===5?[a4]:[])];
      ++leading;
      function go(i,w,M){
        if(i===L){
          if(w!==C)return;
          ++weights;
          for(let h4=0;h4<(L===5?p:1);h4++){
            const h3=mod((1-t)*a4*h4*inv[mod(a3*(s-1))]);
            const h2=mod(-(a3*h3+a4*h4)*inv[a2]);
            if(mod(M+a2*h2*h2+a3*h3*h3+a4*h4*h4-m*(L-1))===0)++constants;
          }
          return;
        }
        for(const {c,k} of patterns[a[i]]){
          if(w+k+4*(L-i-1)<=C)go(i+1,w+k,M+c);
        }
      }
      go(0,0,0);
    }
  }
  for(let s=2;s<p;s++)if(L===4)mask(s);else for(let t=s+1;t<p;t++)mask(s,t);
  return {masks,leading,weights,constants};
}
for(const [L,m,a,w] of [[4,11,132,264],[5,55,5940,900]]){
 const q=tightPencils(L);
 assert(q.masks===m&&q.leading===a&&q.weights===w&&q.constants===0,"tight-pencil census");
 console.log({L,...q});
}

const curveBounds=[];
for(let k=8;k<=11;k++){
 let unionMax=0;
 for(let t=2;t<=6;t++)unionMax=Math.max(unionMax,Math.floor(Math.min(
   14*k-k*(k-1)/t,13*t+1+(k-t)*(14-t))));
 // A residual degree-one polynomial would supply another rational line
 // factor. With k=10 or 11 the residual is therefore constant.
 const n=unionMax+(k<=9?1+14*(10-k):0);
 assert(n<126,"curve bound");
 curveBounds.push(n);
}
assert(curveBounds.join()==="124,118,113,123","curve bounds");
let pairs=0;
for(let a=0;a<=7;a++)for(let b=0;b<=7;b++){
 const N=81-2*a,M=81-2*b;
 const I=Math.min(3*M-2*a,3*N-2*b),d=14*N*M-183*I;
 assert(d>0&&d*d>13*N*(183-N)*M*(183-M),"incidence bound");
 ++pairs;
}
console.log({curveBounds,pairs});
