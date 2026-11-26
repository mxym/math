// Exact finite enumeration of the caterpillar leaf-fiber filtering identity.
const assert=(x,e)=>{if(!x)throw Error(JSON.stringify(e));};
function weightedDeck(go,E,encode){
 const M=new Map();
 for(let mask=0;mask<2**E.length;mask++){
  const P=go.map((_,i)=>i);function r(i){while(P[i]!==i)i=P[i];return i;}
  E.forEach(([a,b],i)=>{if(!(mask&(1<<i)))P[r(a)]=r(b);});
  const comps=new Map();go.forEach(([a,b],i)=>{const j=r(i),k=comps.get(j)??[0,0];k[0]+=a;k[1]+=b;comps.set(j,k);});
  const c=[...comps.values()];if(c.some(x=>x[1]===0))continue;
  const key=c.map(([a,b])=>encode(a,b)).sort((a,b)=>a-b).join(",");
  M.set(key,(M.get(key)||0)+1);
 }
 return JSON.stringify([...M].sort());
}
let checked=0;
for(let n=1;n<=5;n++)for(let x=0;x<3**n;x++){
 const L=[];let a=x;for(let j=0;j<n;j++){L.push(a%3);a=a/3|0;}
 if(n>1&&(!L[0]||!L.at(-1))||n===1&&L[0]<2)continue;
 const core=Array.from({length:n-1},(_,j)=>[j,j+1]),codes=L.map(x=>[x,1]),full=Array.from({length:n},()=>[0,1]),E=core.slice();
 L.forEach((d,j)=>{for(let i=0;i<d;i++){E.push([j,full.length]);full.push([1,0]);}});
 const C=full.length+1, enc=(a,b)=>a+C*b;
 assert(weightedDeck(full,E,enc)===weightedDeck(codes,core,enc),L);checked++;
}
console.log(JSON.stringify({caterpillarsChecked:checked}));