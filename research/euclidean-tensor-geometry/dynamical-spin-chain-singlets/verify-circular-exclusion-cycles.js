// Integer replay of the inductive arc partition. Run with Node.js.
const bit=(x,j)=>(x>>j)&1;
const pop=x=>{let k=0;while(x){x&=x-1;k++;}return k;};
const hop=(x,j,n)=>{
 const h=(j+1)%n;
 if(!bit(x,j)||bit(x,h))throw Error(JSON.stringify({x,j,n}));
 return x^(1<<j)^(1<<h);
};
const lift=(old,d,n)=>{
 const bonds=[];
 for(const j of old.bonds) {
  if(j!==0)bonds.push(j+1);
  else if(d===0)bonds.push(0,1);
  else bonds.push(1,0);
 }
 return {x:((old.x&~1)<<1)|(d<<1)|(old.x&1),bonds};
};
let lists=[[],[{x:1,bonds:[0,1,2]}],[{x:3,bonds:[1,0,2]}]],cases=0,max=0,checks=0;
for(let n=3;n<=14;n++) {
 for(let k=1;k<n;k++){
  const seen=new Set();
  for(const {x,bonds} of lists[k]){
   if(bonds.length!==n||new Set(bonds).size!==n||pop(x)!==k)throw Error("cycle format");
   let y=x;const V=new Set();
   for(const j of bonds){
    const code=y*n+j;
    if(seen.has(code)||V.has(y))throw Error("repeated arc or vertex");
    seen.add(code);V.add(y);y=hop(y,j,n);
   }
   if(y!==x)throw Error("not closed");
  }
  for(let x=0;x<(1<<n);x++)if(pop(x)===k)for(let j=0;j<n;j++)
   if(bit(x,j)&&!bit(x,(j+1)%n)&&!seen.has(x*n+j))throw Error("missing arc");
  cases++;checks+=seen.size;max=Math.max(max,seen.size);
 }
 if(n<14){
  const next=Array.from({length:n+1},()=>[]);
  for(let k=1;k<n;k++)for(const c of lists[k])for(const d of [0,1])next[k+d].push(lift(c,d,n));
  lists=next;
 }
}
console.log(JSON.stringify({cases,checks,max}));