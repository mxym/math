'use strict';
const mod=(x,p)=>(x%p+p)%p;
const norm=(A,B)=>A*A-A*B-B*B;
function assert(ok,msg){if(!ok)throw Error(msg);}
function eg(x,y){
 if(!y)return [Math.abs(x),Math.sign(x),0];
 const [g,p,q]=eg(y,x%y);return [g,q,p-Math.trunc(x/y)*q];
}
function key(A,B,D){
 const [g,u,v]=eg(B,A-B);
 assert(u*B+v*(A-B)===g&&g>0&&D%g===0,'Bezout');
 return [D,g,mod(u*A+v*B,D/g)].join(':');
}
function labels(A,B,D){
 const poss=[[0,0]], seen=new Set([0]), gen=[[A-B,-B],[-B,A]];
 for(let i=0;i<poss.length;i++)for(const [v,w] of gen){
  const [a,b]=poss[i],c=mod(a+v,D),d=mod(b+w,D),k=c*D+d;
  if(!seen.has(k)){seen.add(k);poss.push([c,d]);}
 }
 assert(poss.length===D,'character count');
 const good=x=>{x=mod(x,D);return 4*Math.min(x,D-x)>=D;};
 for(const [a,b] of poss)if(good(a))for(const [c,d] of poss)
  if(good(c)&&good(d-a)&&good(-b-d)&&good(b-c))return [a,b,c,d];
 return null;
}
const checked=new Set(),missing=[],certified=[];
for(let A=-104;A<=104;A++)for(let B=-60;B<=60;B++){
 const D=Math.abs(norm(A,B));if(D<2||D>=1600)continue;
 const id=key(A,B,D);if(checked.has(id))continue;checked.add(id);
 const cert=labels(A,B,D);
 if(!cert){missing.push({A,B,D,id});continue;}
 const [a,b,c,d]=cert;
 for(const [r,s] of [[a,b],[c,d]])assert(mod(r*A+s*B,D)===0&&mod(r*B+s*(A-B),D)===0,'character');
 const steps=[a,c,d-a,-b-d,b-c].map(x=>mod(x,D));
 assert(steps.every(x=>4*Math.min(x,D-x)>=D),'quarter separation');
 certified.push({A,B,D,id,cert});
}
assert(checked.size===685&&certified.length===684,'ideal counts');
assert(missing.length===1&&missing[0].D===4&&missing[0].A%2===0&&missing[0].B%2===0,'unique ideal (2)');
console.log(JSON.stringify({smallIdeals:checked.size,certified:certified.length,missing},null,2));
