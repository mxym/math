'use strict';
const mod=(x,p)=>(x%p+p)%p;
const norm=(A,B)=>A*A-3*B*B;
function assert(ok,msg){if(!ok)throw Error(msg);}
function eg(x,y){
 if(!y)return [Math.abs(x),Math.sign(x),0];
 const [g,p,q]=eg(y,x%y);return [g,q,p-Math.trunc(x/y)*q];
}
function key(A,B,D){
 const [g,u,v]=eg(B,A);
 assert(u*B+v*A===g&&g>0&&D%g===0,'Bezout');
 return [D,g,mod(u*A+v*3*B,D/g)].join(':');
}
function labels(A,B,D){
 const poss=[[0,0]], seen=new Set([0]), gen=[[A,-3*B],[-B,A]];
 for(let i=0;i<poss.length;i++)for(const [v,w] of gen){
  const [a,b]=poss[i],c=mod(a+v,D),d=mod(b+w,D),k=c*D+d;
  if(!seen.has(k)){seen.add(k);poss.push([c,d]);}
 }
 assert(poss.length===D,'character count');
 const good=x=>{x=mod(x,D);return 4*Math.min(x,D-x)>=D;};
 for(const [a,b] of poss)if(good(a))for(const [c,d] of poss)
  if(good(c)&&good(d-a)&&good(2*c-b)&&good(d-2*a)&&good(c-b))return [a,b,c,d];
 return null;
}
const checked=new Set(),missing=[],certified=[];
for(let A=-80;A<=80;A++)for(let B=-46;B<=46;B++){
 const D=Math.abs(norm(A,B));if(D<2||D>=1600)continue;
 const id=key(A,B,D);if(checked.has(id))continue;checked.add(id);
 const cert=labels(A,B,D);
 if(!cert){missing.push({A,B,D,id});continue;}
 const [a,b,c,d]=cert;
 for(const [r,s] of [[a,b],[c,d]])assert(mod(r*A+s*B,D)===0&&mod(3*r*B+s*A,D)===0,'character');
 const steps=[a,c,d-a,2*c-b,d-2*a,c-b].map(x=>mod(x,D));
 assert(steps.every(x=>4*Math.min(x,D-x)>=D),'quarter separation');
 certified.push({A,B,D,id,cert});
}

function dsat(edges,k,max=1e6){
 const n=edges.length,c=Array(n).fill(-1),mask=new Uint32Array(n),cnt=Array.from({length:n},()=>new Uint16Array(k)),u=edges.map(e=>e.length);
 let steps=0;
 function go(d,used){
  if(d===n)return true;
  if(++steps>max)throw Error('budget');
  let v=-1,b=-1,bb=-1;
  for(let i=0;i<n;i++)if(c[i]<0){let r=0,x=mask[i];while(x){r++;x&=x-1;}if(r>b||r===b&&u[i]>bb){v=i;b=r;bb=u[i]}}
  if(b===k)return false;
  for(let t=0;t<Math.min(k,used+1);t++)if(!(mask[v]&(1<<t))){
    c[v]=t;for(let w of edges[v])if(c[w]<0){if(!cnt[w][t]++)mask[w]|=1<<t;u[w]--;}
    if(go(d+1,Math.max(used,t+1)))return true;
    for(let w of edges[v])if(c[w]<0){if(!--cnt[w][t])mask[w]&=~(1<<t);u[w]++;}
    c[v]=-1;
  }
  return false;
 }
 try{return [go(0,0)?c:null,steps]}catch(e){if(e.message==='budget')return [false,steps];throw e}
}

assert(checked.size===1217&&certified.length===1206&&missing.length===11,'finite norm classification');
for(const {A,B,D,id} of missing){
 if([2,4,22,26].includes(D)){
  assert((A+B)%2===0,'reduction to t=1 modulo 2');
 }else if(D===25){
  assert(A%5===0&&B%5===0&&id==='25:5:0','ideal (5)');
 }else{
  assert((D===11||D===13)&&id.split(':')[1]==='1','prime exceptional ideal');
  const t=mod(-Number(id.split(':')[2]),D);
  assert(D===11?(t===5||t===6):(t===4||t===9),'exceptional trace');
 }
}
assert(missing.filter(x=>x.D===11).length===2&&missing.filter(x=>x.D===13).length===2,'prime ideal pairs');
function g12(d,add,mulT,encode,decode,count,one){
 const neg=x=>x.map(a=>mod(-a,d)), n=one.length;
 const step=x=>[...neg(x.slice(n)),...add(x.slice(0,n),mulT(x.slice(n)))];
 const start=[...one,...Array(n).fill(0)],zero=0;
 let x=start,D=[];
 for(let j=0;j<12;j++){D.push(x);x=step(x);}
 assert(encode(x)===encode(start)&&new Set(D.map(encode)).size===12
        &&!D.map(encode).includes(zero),'order twelve steps');
 return Array.from({length:count},(_,i)=>D.map(s=>encode(add(decode(i),s))));
}
const add=(a,b)=>a.map((x,j)=>mod(x+b[j],5));
const enc=a=>a.reduceRight((x,y)=>x*5+y,0);
const dec=i=>[i%5,Math.floor(i/5)%5,Math.floor(i/25)%5,Math.floor(i/125)%5];
const G25=g12(5,add,([x,y])=>[mod(3*y,5),x],enc,dec,625,[1,0]);
const [C25,n25]=dsat(G25,4);
assert(C25&&C25.length===625&&G25.every((E,i)=>E.every(j=>C25[j]!==C25[i])),'4-coloring for ideal (5)');
const neg=[];
for(const [p,t,expected] of [[11,5,2305],[13,4,170202]]){
 const op=(a,b)=>a.map((x,j)=>mod(x+b[j],p)), enc=([x,y])=>p*x+y,
 dec=i=>[Math.floor(i/p),i%p], G=g12(p,op,([x])=>[mod(t*x,p)],enc,dec,p*p,[1]);
 const [C,n]=dsat(G,4);
 assert(C===null&&n===expected,'exhaustive non-4-coloring');
 neg.push({p,t,vertices:G.length,searchNodes:n});
}
console.log(JSON.stringify({smallIdeals:checked.size,circularCertificates:certified.length,missing,
 explicitColoring25:C25.join(''),positiveSearchNodes:n25,nonFourColorable:neg},null,2));
