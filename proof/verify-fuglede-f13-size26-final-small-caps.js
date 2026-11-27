'use strict';

const P=13,mod=x=>(x%P+P)%P;const inv=Array.from({length:P},(_,a)=>Array.from({length:P},(_,b)=>b).find(b=>mod(a*b)===1));
const pts=Array.from({length:169},(_,j)=>[Math.floor(j/P),j%P]);const T=[0,13,1];
const D=pts.map(([x,y])=>pts.map(([u,v])=>x===u?13:mod((v-y)*inv[mod(u-x)])));
const NN=pts.map(([x,y],i)=>D[i].map((d,j)=>14*(d===13?x:mod(y-d*x))+d)); // line id
const stats={}; let max=0,maxparallel=0,for3=0,nodes=0,masks=0;
function run(S){
 const M=Uint8Array.from({length:14},(_,d)=>+S.includes(d));
 let C=pts.flatMap((_,j)=>T.includes(j)||T.some(i=>!M[D[i][j]])?[]:[j]);
 const used=T.slice(), lines=new Uint8Array(182);
 for(let i=0;i<3;i++)for(let j=0;j<i;j++)lines[NN[T[i]][T[j]]]=2;
 function walk(C){
  nodes++;const n=used.length;
  if(n>max)max=n;
  if(n>=9){
   const ps=Array.from({length:14},(_,d)=>Array.from({length:13},(_,i)=>lines[i*14+d]).filter(v=>v===3).length);
   maxparallel=Math.max(maxparallel,...ps);
   if(n>=(stats.maxWitness?.length??0))stats.maxWitness=used.slice();
   if(ps.includes(3))for3++;
  }
  for(let j=0;j<C.length;j++){
   const v=C[j], ids=new Set(used.map(u=>NN[u][v]));
   if([...ids].some(i=>lines[i]===2))continue;
   const prev=[...ids].map(i=>[i,lines[i]]);
   for(const [i,w] of prev)lines[i]=w?w+1:2;
   used.push(v);
   walk(C.slice(j+1).filter(u=>M[D[v][u]]));
   used.pop(); for(const [i,w] of prev)lines[i]=w;
  }
 }
 walk(C);
}
function pick(i,S){if(S.length===5){masks++;run(S);return;}for(let j=i;j<=11;j++)pick(j+1,[...S,j]);}
pick(1,[0,12,13]);
if(max!==4||nodes!==115||masks!==55)throw Error("planar census mismatch");
console.log({max,nodes,masks,...stats});

function fitsProfile(C){
 const counts=Array.from({length:P},(_,t)=>C.reduceRight((z,c)=>mod(z*t+c),0));
 const lifts=(26-counts.reduce((a,b)=>a+b,0))/13;
 return Number.isInteger(lifts)&&lifts>=0&&lifts<=counts.filter(n=>!n).length;
}
let q=0,c=0;
for(let a=1;a<P;a++)for(let b=0;b<P;b++){
 if(fitsProfile([b,0,a]))q++;
 for(let h=0;h<P;h++)if(fitsProfile([b,h,0,a]))c++;
}
if(q||c)throw Error('unexpected nonconstant profile of degree two or three');
console.log({quadraticProfiles:q,cubicProfiles:c});
