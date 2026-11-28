// Exact check of the 3-by-4 quotient table and of the expanded four-path words.
// Usage: node verify_erdos_gyarfas_three_on_one_side.mjs
function verifyShapes(){
 function check(ok,message){if(!ok)throw Error(message);}
 function perms(a){
  return a.length?a.flatMap((v,i)=>perms(a.filter((_,j)=>j!==i)).map(rest=>[v,...rest])):[[]];
 }
 const p=perms([0,1,2]),q=perms([0,1,2,3]);
 const cols=[[1,1,1],...p];
 const tally={};
 function hasMinimum(matrix){
  return matrix.every(row=>row.reduce((sum,x)=>sum+x,0)>=3);
 }
 for(const a of cols)for(const b of cols)for(const c of cols)for(const d of cols){
  const m=[0,1,2].map(i=>[a[i],b[i],c[i],d[i]]);
  if(!hasMinimum(m)||m.some(row=>row.filter(x=>x===2).length>1))continue;
  const key=p.flatMap(pp=>q.map(qq=>pp.flatMap(i=>qq.map(j=>m[i][j])).join(""))).sort()[0];
  tally[key]=(tally[key]??0)+1;
 }
 const expected={
  "111111111111":[1,[1,2,0,1,2,3]],
  "011111112111":[24,[1,2,0,1,2,3]],
  "011111122110":[72,[1,2,0,0,1,2]],
  "011211112110":[36,1],
  "001212102111":[144,0],
  "011211202101":[48,1]
 };
 check(Object.keys(expected).length===Object.keys(tally).length,"type count differs");
 for(const [key,[num,witness]] of Object.entries(expected)){
  check(tally[key]===num,"type multiplicity differs");
  const m=key.match(/..../g).map(row=>[...row].map(Number));
  if(Number.isInteger(witness)){
   const sub=m.map(row=>row.filter((_,j)=>j!==witness));
   check(hasMinimum(sub)&&sub.flat().includes(2),"deletion does not give doubled six-orbit subgraph");
  }else{
   const [V,U,...paths]=witness;
   const counts=Array(4).fill(0);
   for(const j of paths)counts[j]++;
   for(let j=0;j<4;j++){
    if(!counts[j])continue;
    check(m[V][j]===1&&m[U][j]>=counts[j],"matching-path witness invalid");
   }
   check(counts.filter(x=>x===2).length<=1&&counts.every(x=>x<=2),"shared middle configuration invalid");
  }
 }
 return {tally,total:Object.values(tally).reduce((a,b)=>a+b,0)};
}
function verifyPathLemma(){
 function run(n){
  const mod=x=>(x%n+n)%n;
  const mids=[2,3,2,4], tally={4:0,8:0,16:0,skipped:0};
  for(let b=0;b<n;b++)for(let c=0;c<n;c++)for(let d=0;d<n;d++){
   if(c===0){tally.skipped++;continue;}
   const s=[0,b,c,d];
   let word;
   for(let i=0;i<4&&!word;i++)for(let j=i+1;j<4;j++)if(s[i]===s[j]){word=[i,j];break;}
   if(!word){
    const dx=mod(s[0]-s[1]),dy=mod(s[2]-s[3]);
    if(dx===dy)word=[0,1,3,2];
    else if(dx===mod(-dy))word=[0,1,2,3];
    else word=[0,1,2,3,1,0,3,2];
   }
   const seen=new Set([0]);let v=0,x=0;
   function push(layer,coord,returning){
    const id=layer*n+coord;
    if(returning){if(id!==0)throw Error("failure to close");}
    else if(seen.has(id))throw Error("repeated vertex");
    else seen.add(id);
   }
   word.forEach((t,i)=>{
    if(v===0)x=mod(x+s[t]);
    push(mids[t],x,false);
    if(v===1)x=mod(x-s[t]);
    v=1-v;
    push(v,x,i===word.length-1);
   });
   tally[word.length*2]++;
  }
  return [n,tally];
 }
 return [5,6,7,11,31,43,64].map(run);
}
console.log(JSON.stringify({quotients:verifyShapes(),cyclicChecks:verifyPathLemma()},null,2));
