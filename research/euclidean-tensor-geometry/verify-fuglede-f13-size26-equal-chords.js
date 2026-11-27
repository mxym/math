'use strict';
// Every used quotient direction permits only one chord vector up to sign.

const p=13,N=p*p,m=x=>(x%p+p)%p,R=Array.from({length:p},(_,i)=>i),iv=R.map(x=>R.find(y=>m(x*y)===1));
const dir=Array.from({length:N},()=>new Uint8Array(N)),vec=dir.map(()=>new Uint8Array(N));
for(let a=0;a<N;a++)for(let b=0;b<a;b++){let x=m(a%p-b%p),y=m(Math.floor(a/p)-Math.floor(b/p)),d=x?m(y*iv[x]):p,v=Math.min(x+p*y,m(-x)+p*m(-y));dir[a][b]=dir[b][a]=d;vec[a][b]=vec[b][a]=v;}
let hist={};for(let E=-1;E<0;E++){
 let se=[0,1,p],V=new Uint8Array(p+1),max=3,count=0,nodes=0,ex=null;
 for(let i=1;i<3;i++)for(let j=0;j<i;j++){let a=se[i],b=se[j],d=dir[a][b];if(d!==E)V[d]=vec[a][b];}
 function go(lo){
  nodes++;max=Math.max(max,se.length);
  if(se.length===8){count++;ex??=se.slice();return;}
  for(let a=lo;a<N;a++){
   if(a===p)continue;
   let ok=1,add=[];
   for(const b of se){let d=dir[a][b],v=vec[a][b];if(d===E)continue;if(V[d]!==0&&V[d]!==v){ok=0;break;}if(V[d]===0){V[d]=v;add.push(d);}}
   if(ok){se.push(a);go(a+1);se.pop();}
   for(const d of add)V[d]=0;
  }
 }
 go(2);hist[E]={max,count,nodes,ex};
}
if(hist[-1].max!==7||hist[-1].count!==0||hist[-1].nodes!==3134)throw Error("quotient cap census");
console.log(hist[-1]);