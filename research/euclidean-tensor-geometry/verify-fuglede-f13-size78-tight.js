'use strict';
const p=13,m=6,C=21,mod=x=>(x%p+p)%p;
const inv=Array(p).fill(0);
for(let a=1;a<p;a++)for(let b=1;b<p;b++)if(a*b%p===1)inv[a]=b;
const assert=(a,msg)=>{if(!a)throw Error(msg);};
const patterns=Array.from({length:p},()=>[]);
let allQuadraticCount=0;
for(let a=1;a<p;a++)for(let c=0;c<p;c++){
  // Centered residues c+a*t^2; lifted zeros contribute 13 to mass
  // and binom(13,2) to the pair count, wherever those zeros lie.
  const vals=Array.from({length:p},(_,t)=>mod(c+a*t*t));
  const lift=(m*p-vals.reduce((s,n)=>s+n,0))/p;
  if(!Number.isInteger(lift)||lift<0||lift>vals.filter(x=>x===0).length)continue;
  const k=(vals.reduce((s,n)=>s+n*(n-1)/2,0)+lift*p*(p-1)/2-p*m*(m-1)/2)/p;
  assert(Number.isInteger(k)&&k>=4,"small or nonintegral quadratic weight");
  ++allQuadraticCount;
  patterns[a].push({c,k,lift});
}
assert(allQuadraticCount===96,"quadratic count");
console.log({allQuadraticCount});

function tightPencils(L){
  let masks=0,leading=0,weights=0,zeroLiftInputs=0,constants=0;
  const outcomes=new Map();
  function mask(s,t=0){
    ++masks;
    // forms x,y,x+y,x+s*y[,x+t*y]
    for(let a3=1;a3<p;a3++)for(let a4=(L===5?1:0);a4<(L===5?p:1);a4++){
      const a2=mod(-a3*s-a4*t);
      const a0=mod(-a2-a3-a4),a1=mod(-a2-a3*s*s-a4*t*t);
      if(!a0||!a1||!a2)continue;
      const a=[a0,a1,a2,a3,...(L===5?[a4]:[])];
      ++leading;
      const list=[];
      function go(i,w,M,NL){
        if(i===L){
          if(w!==C)return;
          ++weights;
          if(NL===0)++zeroLiftInputs;
          for(let h4=0;h4<(L===5?p:1);h4++){
            const h3=mod((1-t)*a4*h4*inv[mod(a3*(s-1))]);
            const h2=mod(-(a3*h3+a4*h4)*inv[a2]);
            if(mod(M+a2*h2*h2+a3*h3*h3+a4*h4*h4-m*(L-1))!==0)continue;
            ++constants;
            const key=list.slice().sort((a,b)=>a-b).join();
            outcomes.set(key,(outcomes.get(key)||0)+1);
            assert(NL===0,"surviving lifted zero");
          }
          return;
        }
        for(const {c,k,lift} of patterns[a[i]]){
          if(w+k+4*(L-i-1)>C)continue;
          list.push(k);
          go(i+1,w+k,M+c,NL+lift);
          list.pop();
        }
      }
      go(0,0,0,0);
    }
  }
  for(let s=2;s<p;s++)if(L===4)mask(s);else for(let t=s+1;t<p;t++)mask(s,t);
  return {masks,leading,weights,zeroLiftInputs,constants,outcomes:[...outcomes]};
}
for(const [L,m,a,w,z,n,pat] of [[4,11,132,2160,864,48,"4,4,4,9"],[5,55,5940,1800,1800,900,"4,4,4,4,5"]]){
 const q=tightPencils(L);
 assert(q.masks===m&&q.leading===a&&q.weights===w&&q.zeroLiftInputs===z&&q.constants===n,"tight-pencil census");
 assert(JSON.stringify(q.outcomes)===JSON.stringify([[pat,n]]),"wrong surviving pattern");
 console.log({L,...q});
}
