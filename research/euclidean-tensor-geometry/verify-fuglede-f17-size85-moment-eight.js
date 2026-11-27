'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),pow=R.map(x=>R.slice(0,7).map(j=>x**j%p));
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
   if(S===85){
    const w=(q-170)/p;
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
 const ww=Object.keys(hist).map(Number);
 if(d>2)assert(Math.min(...ww)===[6,4,3,2][d-3]&&Math.max(...ww)===[13,15,17,19][d-3],"profile extrema");
}

assert(Object.keys(types[2]).length===0,"quadratics present");
const F=N=>N*N-217*N+12280;
const B=(r,w,d)=>307-Math.ceil(((r+2)*710*d-(r-4)*(16-r)*w)/(30*d));
const cases=[];
for(const [r,w,d] of [[8,431,17],[7,24,1],[6,19,1],[5,17,1],[4,15,1]]){
 const U=B(8,w,d),U2=B(r,431,17),cuts=Math.ceil((F(U)-224)/4);
 assert(U<=97&&cuts>U2,"4-secant contradiction");cases.push({r,U,U2,cuts});
}
assert(JSON.stringify(cases.map(a=>[a.U,a.U2,a.cuts]))===JSON.stringify([[97,97,104],[95,116,117],[90,134,157],[88,150,176],[86,165,198]]),"bounds");
console.log({cases,maxima:Object.fromEntries([3,4,5,6].map(d=>[d,Math.max(...Object.keys(types[d]).map(Number))]))});
