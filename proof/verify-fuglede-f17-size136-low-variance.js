'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
for(let [d,w,count] of [[6,1,1124023],[5,1,209317],[5,2,1668741]]){
 const Q=2*p*w,max=Math.floor(Math.sqrt(Q)),a=Array(d+1).fill(0);
 const L=R.map(x=>R.slice(0,d+1).map(i=>{let a=1;for(let j=0;j<=d;j++)if(i!==j)a=m(a*(x-j)*iv[m(i-j)]);return a;}));
 let tests=0,survive=0;
 function go(i,S,V){
  if(i<=d){
   for(let t=-max;t<=max;t++)if(V+t*t<=Q){a[i]=t;go(i+1,S+t,V+t*t);}
   return;
  }
  tests++;
  for(let x=d+1;x<p;x++){
   let y=m(a.reduce((s,k,j)=>s+k*L[x][j],0));if(y>8)y-=17;
   V+=y*y;S+=y;if(V>Q)return;
  }
  if(V===Q&&S===0)survive++;
 }
 go(0,0,0);
 if(tests!==count||survive)throw Error("variance census");
 console.log({d,w,tests,survive});
}
const W=1124,C=36,V=307,u=18*W-C*V;
for(const [N,upperScaled] of [[136,512*W+784*C],[135,432*W+864*C]]){
 // ||w||^2 >= W^2/V + u^2*N/[17*V*(V-N)].
 if(C*(W*W*17*(V-N)+u*u*N)<=upperScaled*17*V*(V-N))throw Error("indicator mixing bound");
}
