// Finite toy audit of exact event cardinalities; no factoring routine.
// Monic test polynomials are represented solely by their root sets.
let checks=0;
function eq(a,b){checks++;if(a!==b)throw Error(a+' != '+b);}
function* profiles(left,n,pre=[]){
 if(!n){yield pre;return;}
 for(let i=0;i<=left;i++)yield* profiles(left-i,n-1,[...pre,i]);
}
for(const [p,q] of [[3,5],[5,7],[7,11],[11,13]]){
 for(const ds of profiles(p,4)){
  const D=ds.reduce((a,b)=>a+b,0);
  const blocks=[];
  for(let i=0,start=0;i<ds.length;start+=ds[i++]){
   blocks.push(Array.from({length:ds[i]},(_,j)=>start+j));
  }
  let global=0,tagged=0,oneSplit=0;
  for(let x=0;x<p;x++)for(let y=0;y<q;y++){
   if(blocks.some(s=>s.includes(x)&&s.includes(y)))global++;
   if(blocks.some(s=>s.includes(x)||s.includes(y)))tagged++;
   if(blocks[0].includes(x)!==blocks[0].includes(y))oneSplit++;
  }
  eq(global,ds.reduce((a,b)=>a+b*b,0));
  eq(tagged,D*(p+q)-D*D);
  if(ds[0]*2<=p)eq(oneSplit,ds[0]*(p+q)-2*ds[0]*ds[0]);
 }
}
console.log(checks+' exact toy CRT event counts passed.');
