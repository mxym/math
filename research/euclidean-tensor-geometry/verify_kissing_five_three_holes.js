// Run with Node.js. The two witness tables are checked using BigInt fractions.

function audit(h,rows){
 const holes=new Set([0,31,h]), split=h, vars=new Map(), pc=x=>{let k=0;for(;x;x&=x-1)k++;return k;};
 const key=(v,j)=>[pc(v&split),pc(v&(31^split)),+(!!(split&(1<<j))),+(!!(v&(1<<j)))].join(",");
 for(let v=0;v<32;v++)if(!holes.has(v))for(let j=0;j<5;j++)vars.set(key(v,j),[0n,1n]);
 vars.set('rho',[0n,1n]);const active=(v,j)=>!holes.has(v^(1<<j));
 const abs=x=>x<0n?-x:x;
 function gcd(x,y){for(x=abs(x);y;){[x,y]=[y,x%y]}return abs(x);}
 function f(a,b=1){a=BigInt(a);b=BigInt(b);if(b<0n){a=-a;b=-b;}const g=gcd(a,b);return [a/g,b/g];}
 const plus=([a,b],[c,d])=>f(a*d+c*b,b*d), minus=(a,[c,d])=>plus(a,[-c,d]), times=([a,b],[c,d])=>f(a*c,b*d);
 function divide(a,[c,d]){return times(a,f(d,c));}
 let rhs=f(100*(vars.size-1)+400);
 for(const k of vars.keys())vars.set(k,f(100));
 for(const [row,i]of rows){
  const weight=f(i), add=(k,a)=>vars.set(k,plus(vars.get(k),times(a,weight)));
  const [tag,v,w,...t]=row;
  if (!Number.isSafeInteger(i)||i<0) throw Error("invalid row multiplier");
  if (v!==undefined && (!Number.isInteger(v)||v<0||v>=32||holes.has(v))) throw Error("invalid first vertex");
  if (!['rho-lower','rho-upper','norm','upper','active','pair'].includes(tag)) throw Error("unknown row");
  if (tag==='norm' && w!==1 && w!==-1) throw Error("invalid equality orientation");
  if (['active','upper'].includes(tag) && (!Number.isInteger(w)||w<0||w>=5)) throw Error("invalid coordinate");
  let b=f(0);
  if(tag==='rho-lower'){add('rho',f(-1));b=f(-99,25);}
  if(tag==='rho-upper'){add('rho',f(1));b=f(4);}
  if(tag==='norm'){for(let j=0;j<5;j++)add(key(v,j),f(w));add('rho',f(-w));}
  if(tag==='upper'){add(key(v,w),f(1));b=f(1);}
  if(tag==='active'){if(!active(v,w))throw Error("non-active row");add(key(v,w),f(-1));b=f(-4761,10000);}
  if(tag==='pair'){
   add('rho',f(-1,2));
   if(!Number.isInteger(w)||w<0||w>=32||holes.has(w)||![1,2].includes(pc(v^w)))throw Error("invalid pair");
   for(let j=0;j<5;j++){
    if((v^w)&(1<<j)){
     const u=t[j];if(u<=0)throw Error("bad tangent");add(key(v,j),f(-u,200));add(key(w,j),f(-50,u));
    }else{
     if(t[j]!==0&&t[j]!==1)throw Error("bad plane");
     const alpha=active(v,j)?f(69,100):f(0), beta=active(w,j)?f(69,100):f(0);
     const X=divide(t[j]===0?beta:f(1),plus(f(1),alpha)),Y=divide(t[j]===0?alpha:f(1),plus(f(1),beta));
     const C=t[j]===0?minus(minus(times(alpha,beta),times(X,times(alpha,alpha))),times(Y,times(beta,beta))):minus(minus(f(1),X),Y);
     add(key(v,j),X);add(key(w,j),Y);b=minus(b,C);
    }
   }
  }
  rhs=plus(rhs,times(weight,b));
 }
 let min=Infinity;for(const [a,b]of vars.values()){if(a<0n)throw Error("negative column");min=Math.min(min,Number(a)/Number(b));}
 if(rhs[0]>=0n)throw Error("nonnegative RHS");
 return {rhs:rhs.map(String),approx:Number(rhs[0])/Number(rhs[1]),min,variableCount:vars.size};
}
const certificates = [[1,[[["rho-lower"],1033825],[["norm",2,-1],509292],[["upper",2,2],848881],[["norm",6,-1],1018467],[["norm",7,-1],407745],[["upper",7,0],656298],[["norm",14,-1],753647],[["norm",15,-1],261481],[["upper",15,0],290868],[["norm",30,-1],128627],[["pair",2,4,1,254,39,1,1],21514],[["pair",2,6,1,0,81,1,1],817676],[["pair",14,15,125,1,1,1,0],328244],[["pair",15,23,1,1,1,36,278],8281],[["pair",15,30,19,1,1,1,283],37881],[["pair",6,7,111,0,0,1,1],764262],[["pair",6,14,1,1,1,98,1],1620372],[["pair",7,15,1,1,1,110,0],161748],[["pair",14,30,0,1,1,1,124],330891]]],[3,[[["rho-lower"],842532],[["norm",4,-1],442008],[["norm",5,-1],683212],[["active",5,2],171327],[["norm",7,-1],235736],[["upper",7,0],358828],[["norm",12,-1],522711],[["norm",13,-1],932553],[["norm",15,-1],96471],[["upper",15,0],155660],[["norm",28,-1],176181],[["norm",29,-1],294312],[["upper",29,0],7167],[["pair",12,13,100,1,1,1,1],750843],[["pair",12,28,1,1,1,1,100],375421],[["pair",4,12,1,1,0,77,1],374130],[["pair",13,29,1,0,1,1,121],605408],[["pair",4,5,75,1,0,1,1],603496],[["pair",4,8,1,1,307,33,1],93354],[["pair",4,12,1,1,0,85,1],75639],[["pair",5,7,1,135,0,1,1],390397],[["pair",5,13,1,0,1,92,1],1444171],[["pair",7,11,1,1,304,33,1],11083],[["pair",13,15,1,126,1,1,0],160897],[["pair",15,23,1,1,1,17,574],2503],[["pair",28,29,120,0,1,1,1],153208],[["pair",29,30,18,569,1,1,1],40751]]]];
for (const [thirdHole, rows] of certificates) {
  const result = audit(thirdHole, rows);
  if (thirdHole === 1 && result.rhs.join("/") !== "-8772278921/422500") throw Error("Unexpected case-1 total");
  if (thirdHole === 3 && result.rhs.join("/") !== "-6950581251/422500") throw Error("Unexpected case-3 total");
  console.log(thirdHole, result);
}
