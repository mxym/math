'use strict';
const p=17,m=7,C=35,W=987,V=307,mod=x=>(x%p+p)%p,R=Array.from({length:p},(_,i)=>i);
const inv=R.map(a=>R.find(b=>mod(a*b)===1));
const assert=(x,e)=>{if(!x)throw Error(e);};
for(let [d,w,count] of [[6,1,1124023],[5,1,209317],[5,2,1667415]]){
 const Q=34*w,max=Math.floor(Math.sqrt(Q)),a=Array(d+1).fill(0);
 const L=R.map(x=>R.slice(0,d+1).map(i=>{let a=1;for(let j=0;j<=d;j++)if(i!==j)a=mod(a*(x-j)*inv[mod(i-j)]);return a;}));
 let tests=0,survive=0;
 function go(i,S,U){
  if(i<=d){
   for(let t=-Math.min(max,7);t<=max;t++)if(U+t*t<=Q){a[i]=t;go(i+1,S+t,U+t*t);}
   return;
  }
  tests++;
  for(let x=d+1;x<p;x++){
   let y=mod(a.reduce((s,k,j)=>s+k*L[x][j],0));if(y>8)y-=17;
   if(y<-7)return;
   U+=y*y;S+=y;if(U>Q)return;
  }
  if(U===Q&&S===0)survive++;
 }
 go(0,0,0);assert(tests===count&&!survive,"variance census");console.log({d,w,tests,survive});
}
const hist={},q=new Set();
for(let d=2;d<=4;d++){
 const H={};hist[d]=H;
 for(let a=1;a<p;a++)for(let t=0;t<p**(d-1);t++){
  const c=Array.from({length:d-1},(_,i)=>Math.floor(t/p**i)%p);
  const f=R.map(x=>mod(a*x**d+c.reduce((s,b,i)=>s+b*x**i,0)));
  const k=(119-f.reduce((s,x)=>s+x,0))/p;
  if(k%1||k<0||k>f.filter(x=>!x).length)continue;
  const w=(f.reduce((s,x)=>s+x*(x-1)/2,0)+136*k-357)/p;
  assert(Number.isInteger(w)&&w>0,"weight");
  H[w]=(H[w]||0)+1;
  if(d===2)q.add([w,c[0]].join());
 }
 const W=Object.keys(H).map(Number);assert(Math.min(...W)===[8,6,4][d-2]&&Math.max(...W)===[15,19,21][d-2],"catalog bounds");
}
const xy=[...q].map(x=>x.split(",").map(Number)),pat=[];
for(let a=0;a<xy.length;a++)for(let b=a;b<xy.length;b++)for(let c=b;c<xy.length;c++)for(let d=c;d<xy.length;d++){
 const A=[xy[a],xy[b],xy[c],xy[d]];
 if(A.reduce((s,t)=>s+t[0],0)!==35||mod(A.reduce((s,t)=>s+t[1],0))!==4)continue;
 pat.push(A.sort((a,b)=>a[0]-b[0]||a[1]-b[1]));
}
assert(JSON.stringify(pat)===JSON.stringify([[[8,15],[9,5],[9,9],[9,9]]]),"quadratic tight pattern");
for(let d=10;d<=12;d++){
 let z=18;
 for(let k=2;k<=d;k++)for(let t=2;t<=Math.min(k,d-5);t++)
  z=Math.max(z,Math.min(18*k-Math.ceil(k*(k-1)/t),17*k+1-(k-t)*(t-1)));
 assert(z<=17*(d-1)+2,"rational line union");
}
const u=18*W-C*V;
for(const [N,upper] of [[136,343*W+C*(1225-343)],[152,349*W+C*(120*10+876)],[135,343*W+C*(1225-343)],[151,313*W+C*(1225-313)],[131,313*W+C*(1225-313)]]){
 assert(C*(W*W*17*(V-N)+u*u*N)>upper*17*(V-N),"indicator contradiction");
}
assert(C*151===6*W-2*(12*21+14)-3*C,"quartic support");
assert(C*130<5*W-(13*19+16)-3*C&&W%C===7,"cubic support and final divisibility");
console.log({hist,pat});
