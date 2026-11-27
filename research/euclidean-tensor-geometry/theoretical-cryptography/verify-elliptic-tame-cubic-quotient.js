// F4=F2[t]/(t²+t+1), with elements encoded in two bits.
const F=[0,1,2,3], U=F.slice(1);
function mul(x,y){let z=0;while(y){if(y&1)z^=x;x<<=1;if(x&4)x^=7;y>>=1;}return z;}
const pow=(x,s)=>s===1?x:mul(x,x);
const div=(x,y)=>mul(x,pow(y,2));
let checks=0;
function eq(x,y){checks++;if(x!==y)throw Error(x+' != '+y);}
for(const r of [2,3,4]){
 const lines=new Set();
 for(const x of F)for(const y of F){
  if(!(x||y)||(r===2&&!(x&&y))||(r===3&&!x))continue;
  lines.add(x ? div(y,x) : 'infinity');
 }
 eq(lines.size,r+1);
}
for(const u of U)for(const v of U)for(const s of [1,2])for(const swap of [0,1]){
 const fixed=U.filter(x=>x===div(mul(v,pow(swap?1:x,s)),mul(u,pow(swap?x:1,s)))).length;
 eq(fixed,swap!==(s-1)?1:u===v?3:0);
}
for(const u of U)for(const b of F)for(const s of [1,2]){
 const fixed=F.filter(x=>x===(mul(u,pow(x,s))^b)).length;
 eq(fixed,s===1?(u!==1?1:b===0?4:0):(b===0||b===div(1,u)?2:0));
}
console.log(checks+' exact finite field checks passed.');

const mod=x=>(x%13+13)%13;
const halves=(X,Y)=>{
 const pts=[];
 for(let x=0;x<13;x++)for(let y=1;y<13;y++){
  if(mod(y*y-x*x*x-5))continue;
  let m=0;
  for(;mod(2*y*m-3*x*x);m++);
  const X2=mod(m*m-2*x), Y2=mod(m*(x-X2)-y);
  if(X===X2&&Y===Y2)pts.push([x,y]);
 }
 return pts;
};
eq(JSON.stringify(halves(2,0)),JSON.stringify([[7,6],[7,7],[10,2],[10,11]]));
eq(halves(4,11).length,0);
console.log('Two F13 genus-one halving checks passed.');
