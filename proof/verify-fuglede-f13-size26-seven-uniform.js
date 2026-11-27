'use strict';

const p=13,R=Array.from({length:p},(_,i)=>i),mod=x=>(x%p+p)%p,IV=R.map(a=>R.find(b=>mod(a*b)===1));
function solve(A,B){let M=A.map((x,i)=>[...x,mod(B[i])]),n=A.length;for(let j=0;j<n;j++){let k=M.findIndex((x,i)=>i>=j&&x[j]);if(k<0)throw Error("rank");[M[j],M[k]]=[M[k],M[j]];M[j]=M[j].map(x=>mod(x*IV[M[j][j]]));for(let i=0;i<n;i++)if(i!==j){let f=M[i][j];M[i]=M[i].map((x,k)=>mod(x-f*M[j][k]));}}return M.map(x=>x[n]);}
const Q4=R.map(()=>[]),Q5=R.map(()=>[]);
for(let d of [4,5])for(let a of R.slice(1))for(let b of R)for(let c of R)for(let e of R)for(let f of (d===5?R:[0])){
 let K=d===4?[e,c,b,0,a]:[f,e,c,b,0,a],V=R.map(x=>mod(K.reduce((s,g,i)=>s+g*x**i,0)));
 if(V.reduce((s,n)=>s+n)!==26||Math.max(...V)>6)continue;
 (d===4?Q4:Q5)[a].push({K,V});
}

'use strict';

const r=R,m=mod,i=IV;
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const masks={};
function choose(S,k){if(S.length===7){let [j,t]=canonical(S);masks[j]=t;return;}for(let x=k;x<=13-(7-S.length);x++)choose([...S,x],x+1);}choose([0,1,13],2); // initial slope ordering is immaterial

const RESULTS={},MASKS=Object.values(masks);if(MASKS.length!==5)throw Error("five orbits required");
for(let S of MASKS){let F=S.map(s=>s===13?[0,1]:[1,s]),P=d=>R.slice(0,d+1).map(j=>F.map(([x,y])=>mod(x**(d-j)*y**j)));
 let V=F.map(([a,b])=>R.flatMap(x=>R.map(y=>mod(a*x+b*y))));
 let A=P(4),B=P(3),D=P(5),result={q:0,c:0,qgood:0,cgood:0,profiles:{},witness:null};
 function test(a,h,pool,quintic){
  let L=a.map((x,i)=>pool[x].map(E=>R.map(t=>E.V[mod(t-h[i])])));if(L.some(l=>!l.length))return;
  let P=[];function go(j){
   if(j<7){for(let o of L[j]){P.push(o);go(j+1);P.pop();}return;}
   for(let k=0;k<p*p;k++){let f=P.reduce((s,o,i)=>s+o[V[i][k]],0)-12;if(f%13)return;}
   if(quintic)result.q++;else result.c++;
   let H={};for(let k=0;k<p*p;k++){let f=(P.reduce((s,o,i)=>s+o[V[i][k]],0)-12)/13;if(f<0||f>2)return;H[f]=(H[f]||0)+1;}
   if(quintic)result.qgood++;else result.cgood++;
   let q=JSON.stringify(H);result.profiles[q]=(result.profiles[q]||0)+1;result.witness??={a,h,P:P.slice()};
  }
  go(0);
 }
 let a5=solve(D.map(x=>x.slice(0,6)),D.map(x=>-x[6])).concat([1]);
 if(a5.every(x=>x))test(a5,Array(7).fill(0),Q5,true);
 for(let a5 of R.slice(1))for(let a6 of R.slice(1)){
  let a=solve(A.map(x=>x.slice(0,5)),A.map(x=>-x[5]*a5-x[6]*a6)).concat([a5,a6]);if(a.some(x=>!x||!Q4[x].length))continue;
  let B2=B.map(x=>x.slice(2,6).map((g,i)=>mod(g*a[i+2])));
  for(let h6 of R){
   let h=[0,0,...solve(B2,B.map(x=>-x[6]*a6*h6)),h6];test(a,h,Q4,false);
  }
 }
 RESULTS[S.join()]=result;
}
if(Object.values(RESULTS).some(o=>o.q||o.c))throw Error("K7 projection occurs");
console.log(RESULTS);
