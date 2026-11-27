const md=(v,q)=>(v%q+q)%q;
function rem(c,P,q){const n=P.length-1;const B=c.slice();for(let i=B.length-1;i>=n;i--){const x=B[i];for(let j=0;j<=n;j++)B[i-n+j]=md(B[i-n+j]-x*P[j],q);}return B.slice(0,n).every(x=>md(x,q)===0);}
function test(q,d,h,base){
 const Q=q**d,J=base.length,steps=1<<J,min=Array(steps).fill(Infinity),freq=Array(steps).fill(0);
 const factors=base.map(G=>Array.from({length:h*(G.length-1)+1},(_,i)=>i%h?0:G[i/h]));
 for(let id=0;id<Q;id++){
  const v=Array.from({length:d},(_,i)=>Math.floor(id/q**i)%q);
  const vr=Array.from({length:h},(_,l)=>v.filter((_,i)=>i%h===l));let zero=0;
  for(let j=0;j<J;j++){const p=rem(v,factors[j],q),b=vr.every(x=>rem(x,base[j],q));if(p!==b)throw Error("factor block mismatch");if(p)zero|=1<<j;}
  freq[zero]++;if(!id)continue;
  const E=v.reduce((s,x)=>s+Math.min(x,q-x)**2,0);for(let mask=0;mask<steps;mask++)if((zero|mask)===(steps-1))min[mask]=Math.min(min[mask],E);
 }
 const p1=Array.from({length:Math.min(q*q,6)},(_,e)=>freq.reduce((s,x,j)=>s+(min[j]<=e+1?x:0),0));
 return {q,d,h,Q,min:min.map(x=>x===Infinity?null:x),freq,p1};
}
const result=[test(3,8,2,[[2,1,1],[2,2,1]]),test(5,4,1,[[2,0,1],[3,0,1]])];
console.log(JSON.stringify(result));
