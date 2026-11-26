"use strict";
// Exact verifier for the nine proper hexagons in the sharpness construction.
// Coordinates scaled by 128; the affine plane has sum 256.
const P = [[4,0,0],[0,4,0],[0,0,4]];
for (let i=0;i<3;i++) for (let j=0;j<3;j++) if(i!==j) {
  const p=[0,0,0]; p[i]=3; p[j]=1; P.push(p);
}
const family=P.map(p=>p.map(x=>x*32));
const full=(1<<P.length)-1;
function meets(mask,hex) {
  if(!mask) return true;
  const lo=[-Infinity,-Infinity,-Infinity], hi=[Infinity,Infinity,Infinity];
  for(let i=0;i<family.length;i++) if(mask&(1<<i)) for(let j=0;j<3;j++){
    lo[j]=Math.max(lo[j],family[i][j]-(hex?4:0));
    if(hex) hi[j]=Math.min(hi[j],family[i][j]+132);
  }
  return lo.every((l,j)=>l<=hi[j]) &&
    lo.reduce((a,b)=>a+b,0)<=256 && hi.reduce((a,b)=>a+b,0)>=256;
}
let quads=0,pairs=0,minimum=4;
for(let mask=0;mask<=full;mask++){
  if(meets(mask,false)!==meets(mask,true)) throw Error("nerve changed");
  const bits=P.map((_,i)=>1<<i).filter(b=>mask&b);
  if(bits.length===2){pairs++;if(!meets(mask,true))throw Error("disjoint pair");}
  if(bits.length===4){quads++;if(!bits.some(b=>meets(mask^b,true)))throw Error("(4,3) failed");}
  if(meets(mask,true)&&meets(full^mask,true)) throw Error("two points suffice");
  if(meets(mask,true)) for(let sub=full^mask;;sub=(sub-1)&(full^mask)){
    if(meets(sub,true)&&meets(full^mask^sub,true)){minimum=3;break;}
    if(!sub)break;
  }
}
if(minimum!==3) throw Error("no three-way partition");
console.log({pairs,quads,subfamilies:full+1,minimum});
