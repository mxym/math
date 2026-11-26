'use strict';
const check=(x,msg)=>{if(!x)throw Error(msg);};
const key=S=>S.slice().sort((a,b)=>Math.abs(a)-Math.abs(b)).join(',');
const parse=s=>s?s.split(',').map(Number):[];
const sizes=n=>Array.from({length:n},(_,i)=>i+1);
function rev(S,n){
  const C=sizes(n), sk=key(S);
  if(sk===key(C))return null;
  const i=C.find(i=>!S.some(x=>Math.abs(x)===i));
  if(S.every(x=>x>0))return [i,[...S,i],[-i]];
  if(S.length<n-1)return [i,[i],[...S,-i]];
  const u=S.find(x=>x>0)??S[0];
  return [i,[u,i],[...S.filter(x=>x!==u),-i]];
}
function valid(S,i,A,B){
  check(!S.some(x=>Math.abs(x)===i),'pivot in resolvent');
  check(A.includes(i)&&B.includes(-i),'pivot absent');
  check(new Set(A.map(Math.abs)).size===A.length&&new Set(B.map(Math.abs)).size===B.length,'invalid premise');
  check(key([...new Set([...A.filter(x=>x!==i),...B.filter(x=>x!==-i)])])===key(S),'bad resolvent');
}
function verify(n){
  const C=key(sizes(n)), F=new Set;
  for(let a=0;a<(1<<n);a++)F.add(key(sizes(n).map((i,k)=>a&(1<<k)?-i:i)));
  for(let a=0;a<(1<<n);a++){
    const bad=[...F].filter(s=>parse(s).every(x=>!!(a&(1<<(Math.abs(x)-1)))===(x<0)));
    check(bad.length===1,'not a minimally unsatisfiable cover');
  }
  function finish(S){
    const i=sizes(n).find(x=>!S.some(y=>Math.abs(y)===x));
    if(!i){check(F.has(key(S)),'nonformula terminal');return key(S)===C?1n:0n;}
    const A=[...S,i],B=[...S,-i];valid(S,i,A,B);
    return finish(A)+finish(B);
  }
  const add=(m,s,k)=>m.set(s,(m.get(s)||0n)+k);
  let M=new Map([['',1n]]),first=null,table=null;
  for(let d=1;d<=512;d++){
    const T=new Map;
    for(const [s,k] of M){
      const S=parse(s),r=rev(S,n);
      if(!r){add(T,s,2n*k);continue;}
      const [i,A,B]=r;valid(S,i,A,B);
      for(const U of [A,B]){
        check(U.length<n||key(U)===C,'state overflow');
        add(T,key(U),k);
      }
    }
    M=T;
    const D=1n<<BigInt(d);
    check([...M.values()].reduce((x,y)=>x+y,0n)===D,'mass leakage');
    let a=0n;
    for(const [s,k] of M){
      const S=parse(s);a+=k*finish(S)*(1n<<BigInt(S.length));
    }
    const Q=D*(1n<<BigInt(n));
    if(BigInt((2*n-3)**2)*a>25n*BigInt(F.size-1)*(Q-a)&&first===null)first=d;
    if(d===46)table=[a.toString(),Q.toString(),M.size];
  }
  check(first!==null,'no test certificate');
  return {variables:n,clauses:F.size,firstDepth:first,atDepth46:table};
}
for(const n of [3,4,5]) (typeof console==='undefined'?text:console.log)(verify(n));
