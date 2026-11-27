function grid78(){
const p=13,mod=x=>(x%p+p)%p,inv=Array(p).fill(0);for(let a=1;a<p;a++)for(let b=1;b<p;b++)if(a*b%p===1)inv[a]=b;
const seen=new Set(),orbits=[];
for(let mask=0;mask<1<<p;mask++){
 const X=Array.from({length:p},(_,i)=>i).filter(i=>mask&(1<<i));
 if(X.length!==6||seen.has(mask))continue;
 orbits.push(X);
 for(let a=1;a<p;a++)for(let b=0;b<p;b++)seen.add(X.reduce((s,x)=>s|(1<<mod(a*x+b)),0));
}
function weights(X){return X.map(s=>inv[X.reduce((z,x)=>x===s?z:mod(z*(s-x)),1)]);}
let pairs=0,rowTuples=0,matrices=0,examples=[];
for(let X of orbits)for(let Y of orbits){
 ++pairs;
 const W=weights(X),V=weights(Y);
 for(let c=0;c<p;c++){
  const rows=X.map((x,i)=>{
   const tab=Array.from({length:p},()=>new Uint8Array(p)),L=[];
   for(let v=0;v<p;v++)for(let w=0;w<p;w++){
    const z=Y.map((y,j)=>mod(W[i]*V[j]*(c*y*y+v*y+w)));
    if(z.every(q=>q<=6)&&z.reduce((s,q)=>s+q,0)===p){tab[v][w]=1;L.push([v,w]);}
   }
   return {tab,L};
  });
  if(rows.some(r=>r.L.length===0))continue;
  const inds=[0,1,2,3,4,5].sort((i,j)=>rows[i].L.length-rows[j].L.length);
  const [i0,i1,i2,...irest]=inds;
  const x0=X[i0],x1=X[i1],x2=X[i2];
  const interp=X.map(x=>[
     mod((x-x1)*(x-x2)*inv[mod((x0-x1)*(x0-x2))]),
     mod((x-x0)*(x-x2)*inv[mod((x1-x0)*(x1-x2))]),
     mod((x-x0)*(x-x1)*inv[mod((x2-x0)*(x2-x1))])]);
  for(const [v0,w0] of rows[i0].L) for(const [v1,w1] of rows[i1].L){
   const b=mod((v1-v0)*inv[mod(x1-x0)]),e=mod(v0-b*x0);
   const v2=mod(b*x2+e);
   for(let w2=0;w2<p;w2++){
    if(!rows[i2].tab[v2][w2])continue;
    ++rowTuples;
    const ww=X.map((x,i)=>mod(interp[i][0]*w0+interp[i][1]*w1+interp[i][2]*w2));
    if(!irest.every(i=>rows[i].tab[mod(b*X[i]+e)][ww[i]]))continue;
    const F=X.map((x,i)=>Y.map((y,j)=>mod(W[i]*V[j]*(c*y*y+mod(b*x+e)*y+ww[i]))));
    if(!Y.every((_,j)=>F.reduce((s,r)=>s+r[j],0)===p))continue;
    ++matrices;
    if(examples.length<5)examples.push({X,Y,F});
   }
  }
 }
}
return {orbits,pairs,rowTuples,matrices,examples};
}

const result=grid78();
if(result.orbits.length!==14||result.pairs!==196||result.rowTuples!==1742||result.matrices!==4)throw Error(JSON.stringify(result));
const A="0,1,2,4,5,6",B="0,2,3,4,5,7";
for(const {X,Y,F} of result.examples){
 if(!((X.join()===A&&Y.join()===B)||(X.join()===B&&Y.join()===A))||!F.some(row=>row.includes(6)))
  throw Error("bad affine class or cap");
}
console.log(result);
function testSmallProfiles(){
 const p=13,mod=x=>(x%p+p)%p;
 let qUnique=0,cUniform=0,cOther=0;
 for(let a=0;a<p;a++)for(let b=0;b<p;b++)for(let c=0;c<p;c++)for(let d=0;d<p;d++){
  let vals=Array.from({length:p},(_,x)=>mod(a+x*(b+x*(c+x*d))));
  if(vals.reduce((s,n)=>s+n,0)!==78||Math.max(...vals)>9)continue;
  if(vals.every(x=>x===6))++cUniform;
  else {
   const q=vals.reduce((s,n)=>s+n*(n-1)/2,0);
   if((q-13*15)/13!==3)throw Error("bad cubic");
   ++cOther;
  }
 }
 for(let a=0;a<p;a++)for(let b=0;b<p;b++)for(let c=0;c<p;c++)for(let d=0;d<p;d++)for(let e=0;e<p;e++){
  let sum=0,cap=0;
  for(let x=0;x<p;x++){const n=mod(a+x*(b+x*(c+x*(d+x*e))));sum+=n;cap=Math.max(cap,n);}
  if(sum===78&&cap<=7){
   if(a!==6||b||c||d||e)throw Error("bad quartic");
   ++qUnique;
  }
 }
 if(qUnique!==1||cUniform!==1||cOther!==104)throw Error("profile counts");
 console.log({qUnique,cUniform,cOther});
}
testSmallProfiles();
