'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),pow=R.map(x=>R.slice(0,8).map(j=>x**j%p));
const assert=(b,e)=>{if(!b)throw Error(e);};
const H=new Uint8Array(17),types={},qset=new Set();
for(let d=2;d<=6;d++){
 const A=Array(d+1).fill(0),hist={};types[d]=hist;
 function rec(j){
  if(j<=d-2){for(let t=0;t<p;t++){A[j]=t;rec(j+1);}return;}
  H.fill(0);let S=0,q=0;
  for(let x=0;x<p;x++){
   let y=0;for(let k=1;k<=d;k++)y+=A[k]*pow[x][k];y%=p;
   H[y]++;S+=y;q+=y*(y-1)/2;
  }
  for(let c=0;c<p;c++){
   const ell=(68-S)/17;if(ell===0){
    const w=(q+136*ell-102)/p;
    assert(Number.isInteger(w)&&w>0,"weight");
    hist[w]=(hist[w]||0)+1;
    if(d===2)qset.add([w,c].join());
   }
   const z=H[p-1-c];
   q+=S-136*z;
   S+=p-p*z;
  }
 }
 for(let a=1;a<p;a++){A[d]=a;rec(1);}
 const ww=Object.keys(hist).map(Number);if(d<4&&ww.length||d>=4&&(ww[0]!==[4,3,2][d-4]||ww.at(-1)!==[11,12,16][d-4]))throw Error("mass68 extrema"); console.log({d,min:ww[0],max:ww.at(-1),count:Object.values(hist).reduce((a,b)=>a+b,0)});}

const W68=570n,C68=26n,V68=307n,P68=17n;
function indicator(na){const D=P68*V68*(V68-na),z=18n*W68-C68*V68;return [W68*W68*P68*(V68-na)+z*z*na,D];}
function above(na,s){const [l,d]=indicator(na);return C68*l>W68*s*d;}
if(26n*169n>=8n*570n-10n*16n||26n*170n<8n*570n-10n*16n||above(224n,172n)||!above(225n,172n))throw Error("support interval");
let ex=0,min=null;
for(let n=170n;n<=224n;n++)for(let m=n;m<=224n;m++){
 const bound=(n,m)=>8n*m-10n+(26n*n-4560n+160n)/2n;
 const x=bound(n,m),y=bound(m,n),e=x<y?x:y;
 const t=18n*n*m-307n*e,Q=t*t-17n*n*(307n-n)*m*(307n-m);
 if(t<=0n||Q<=0n)throw Error("unweighted incidence bounds");
 ++ex;if(min===null||Q<min)min=Q;
}
console.log({support:[170,224],ex,min:min.toString()});
