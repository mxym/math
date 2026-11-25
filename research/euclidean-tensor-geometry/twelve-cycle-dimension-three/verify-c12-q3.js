'use strict';
const P=1009, K=[[1,1,1],[1,2,3],[1,4,5]], s=6;
const mod=x=>(x%P+P)%P;
function pow(x,e){let a=1;while(e){if(e&1)a=a*x%P;x=x*x%P;e>>=1;}return a;}
const words=[];
for(let index=0;index<3**s;index++){
 if(index===1)continue;
 let a=index;words.push(Array.from({length:s},()=>{const b=a%3;a=(a-b)/3;return b;}));
}
const n=words.length;
const M=words.map(u=>Int32Array.from(words,v=>{
 let z=1;for(let j=0;j<s;j++)z=z*K[u[j]][v[j]]*K[v[j]][u[(j+1)%s]]%P;
 return z;
}));
let det=1, piv=[];
for(let j=0;j<n;j++){
 let i=j;while(i<n&&!M[i][j])i++;
 if(i===n)throw Error('zero pivot at '+j);
 if(i!==j){[M[i],M[j]]=[M[j],M[i]];det=mod(-det);}
 const d=M[j][j];piv.push(d);det=det*d%P;
 const inv=pow(d,P-2);
 for(let a=j+1;a<n;a++)if(M[a][j]){
  const scale=M[a][j]*inv%P;
  for(let b=j+1;b<n;b++)M[a][b]=mod(M[a][b]-scale*M[j][b]);
  M[a][j]=0;
 }
}
const report={n,det,first:piv.slice(0,8),last:piv.slice(-8)};
if(n!==728||det!==727||report.first.join(',')!=='1,4,1,1007,16,1007,494,294'||report.last.join(',')!=='816,176,583,463,545,383,331,706')throw Error(JSON.stringify(report));
console.log(JSON.stringify(report));
