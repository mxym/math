'use strict';
// Local graph test for size-39 layered members from moments through five.
const p=13,mod=x=>(x%p+p)%p;
const inv=Array.from({length:p},(_,x)=>Array.from({length:p},(_,y)=>y).find(y=>mod(x*y)===1));
const chk=(x,msg)=>{if(!x)throw Error(msg);};
const bin=[];for(let i=0;i<=7;i++)bin[i]=Array.from({length:i+1},(_,j)=>j===0||j===i?1:bin[i-1][j]+bin[i-1][j-1]);
const pw=Array.from({length:p},(_,x)=>Array.from({length:10},(_,i)=>mod(x**i)));
const graphs=[];let trials=0,parabolas=0;
for(let d=2;d<=9;d++){
 const a=Array(d+1).fill(0);a[d]=1;
 function enumA(i){
  if(i<d-1){for(let r=0;r<p;r++){a[i]=r;enumA(i+1);}return;}
  trials++;
  for(const k of [11,12]){
   let q=0;for(let j=2;j<=d;j++)if(k-j>=2&&k-j<=d)q+=a[j]*a[k-j];
   if(mod(q))return;
  }
  const f=pw.map(row=>mod(a.reduce((s,x,j)=>s+x*row[j],0)));
  if(mod(f.reduce((s,x)=>s+x**3,0)))return;
  for(let s=0;s<p;s++){
   const c=new Uint8Array(p);
   for(let x=0;x<p;x++)if(++c[mod(f[x]-s*x)]>3)return;
  }
  const M=[];for(let k=4;k<=4;k++)M[k]=Array.from({length:k+1},(_,j)=>mod(bin[k][j]*f.reduce((s,y,x)=>s+pw[x][k-j]*pw[y][j],0)));
  if(M[4].every(x=>x===0)){chk(d===2,'quartic-zero graph not parabolic');parabolas++;return;}
  graphs.push({f,M});
 }
 enumA(2);
}
chk(trials===5229044&&parabolas===1&&graphs.length===62,'local graph census');
console.log({trials,parabolas,nonzeroQuarticGraphs:graphs.length});
const counts={13:1}; // The parabola has all thirteen nonvertical slopes.
for(const {f} of graphs){
 const slopes=new Set();
 for(let i=0;i<p;i++)for(let j=0;j<i;j++)slopes.add(mod((f[i]-f[j])*inv[i-j]));
 counts[slopes.size]=(counts[slopes.size]??0)+1;
}
chk(JSON.stringify(counts)===JSON.stringify({11:6,12:14,13:43}),"slope census");
console.log({counts});

const c2=[],c3=[];
function fits(values){
 const k=(39-values.reduce((s,x)=>s+x,0))/13;
 return Number.isInteger(k)&&k>=0&&k<=values.filter(x=>!x).length?k:null;
}
for(let a=1;a<p;a++)for(let c=0;c<p;c++){
 const q=Array.from({length:p},(_,t)=>mod(a*t*t+c));
 if(fits(q)!==null)c2.push([a,c,fits(q)]);
 for(let b=0;b<p;b++){
  const r=Array.from({length:p},(_,t)=>mod(a*t**3+b*t+c));
  if(fits(r)!==null)c3.push([a,b,c,fits(r)]);
 }
}
chk(c2.length===0,"quadratic profile census");
chk(JSON.stringify(c3)===JSON.stringify([[2,0,3,0],[3,0,3,0],[4,0,9,0],[6,0,9,0],[7,0,9,0],[9,0,9,0],[10,0,3,0],[11,0,3,0]]),"cubic profile census");
console.log({quadraticProfiles:c2.length,cubicProfiles:c3.length});
