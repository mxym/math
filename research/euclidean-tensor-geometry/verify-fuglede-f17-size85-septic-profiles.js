'use strict';
{
const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
for(const cap of [9,10])for(let d=3;d<=(cap===9?7:6);d++){
 const A=R.slice(0,d+1),B=A.map(i=>{
  let g=[1],den=1;
  for(const j of A)if(j!==i){
   const w=Array(g.length+1).fill(0);for(let k=0;k<g.length;k++){w[k]=m(w[k]-j*g[k]);w[k+1]=m(w[k+1]+g[k]);}g=w;den=m(den*(i-j));
  }
  return g.map(v=>m(v*iv[den]));
 });
 const j=A.findLast(b=>B[b][d-1]!==0);
 const P=R.map(x=>B.map(g=>m(g.reduce((s,a,i)=>s+a*x**i,0))));
 const v=new Uint8Array(17),free=A.filter(t=>t!==j);let count=0,max=0,ex;
 
 function go(i,S,Q,L,V){
  if(i<free.length){
   const x=free[i],b=B[x][d-1],l=B[x][d];
   for(let a=0;a<=cap;a++){v[x]=a;go(i+1,S+a,Q+a*a,L+a*b,V+a*l);}return;
  }
  const a=m(-L*iv[B[j][d-1]]);if(a>cap||!m(V+a*B[j][d]))return;
  v[j]=a;S+=a;Q+=a*a;
  for(let x=d+1;x<p;x++){
   const row=P[x];let n=0;for(let k=0;k<=d;k++)n+=row[k]*v[k];n%=p;
   if(n>cap||S+n>85||(S+n)+(16-x)*cap<85)return;
   S+=n;Q+=n*n;v[x]=n;
  }
  if(S!==85)return;count++;
  if(Q>max){max=Q;ex=Array.from(v);}
 }
 go(0,0,0,0,0);if(count!==(cap===9?[0,12,64,1360,21920]:[0,24,336,5864])[d-3]||count&&(max-425)/34!==(cap===9?[0,4,4,6,6]:[0,8,7,8])[d-3])throw Error("low-peak profile catalogue"); console.log({cap,d,count,max});
}
}
