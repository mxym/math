'use strict';

const P = 13;
const N = P*P;
const mod = x => (x%P+P)%P;
const inv = Array(P).fill(0);
for (let a=1; a<P; ++a)
  for (let b=1; b<P; ++b)
    if (a*b%P===1) inv[a]=b;
const dir = (a,b) => {
  const dx = mod(a%P-b%P);  
  return dx===0 ? P
    : mod((Math.floor(a/P)-Math.floor(b/P))*inv[dx]);
};
const dirs = Array.from({length:N},(_,a)=>
  Uint8Array.from({length:N},(_,b)=>dir(a,b)));
const intercept = (a,s) => s===P ? a%P
    : mod(Math.floor(a/P)-s*(a%P));
const T = [0,1,P];
const forced = (1<<0)|(1<<(P-1))|(1<<P);

function check(maxDirs, lineCap, targetSize) {
  let masks=0, nodes=0, completions=0, max=3;const sets=[];
  function searchMask(mask) {
    ++masks;
    const candidates=[];
    for (let a=2;a<N;++a)
      if (a!==P && T.every(t=>mask&(1<<dirs[a][t])))
        candidates.push(a);
    const chosen=T.slice();
    const counts=new Uint8Array((P+1)*P);
    const update=(a,delta)=>{
      for(let s=0;s<=P;++s) counts[s*P+intercept(a,s)]+=delta;
    };
    for(const t of T) update(t,1);
    function dfs(cs) {
      ++nodes;
      max=Math.max(max,chosen.length);
      if(chosen.length===targetSize){++completions;sets.push(chosen.slice());return;}
      for(let i=0;i<cs.length;++i) {
        const a=cs[i];
        if(chosen.some(b=>{
          const s=dirs[a][b];
          return counts[s*P+intercept(a,s)]>=lineCap;
        })) continue;
        const tail=[];
        for(let j=i+1;j<cs.length;++j)
          if(mask&(1<<dirs[a][cs[j]])) tail.push(cs[j]);
        chosen.push(a);
        update(a,1);
        dfs(tail);
        update(a,-1);
        chosen.pop();
      }
    }
    dfs(candidates);
  }
  function enumerate(mask,next,left) {
    if(left===0){searchMask(mask);return;}
    for(let s=next;s<P-1;++s) enumerate(mask|(1<<s),s+1,left-1);
  }
  enumerate(forced,1,maxDirs-3);
  return {maxDirs,lineCap,targetSize,masks,nodes,max,completions,sets};
}

const checkEq=(x,y)=>{if(x!==y)throw Error(x+" != "+y);};
const H=[0,1,3,9],Hstar=H.slice(1);
const cases=[
  [4,6,7,11,53,0], [5,4,8,55,880,0], [5,4,7,55,880,9],
  [9,4,11,462,2851982,0], [9,3,10,462,1531034,0]
];
function binaryCross(A) {
  const ps=new Set(A);
  for(const c of A)for(const a of A)for(const b of A){
    const u=[mod(a%P-c%P),mod(Math.floor(a/P)-Math.floor(c/P))];
    const v=[mod(b%P-c%P),mod(Math.floor(b/P)-Math.floor(c/P))];
    if(mod(u[0]*v[1]-u[1]*v[0])===0)continue;
    const on=(t,z)=>mod(c%P+t*z[0])+P*mod(Math.floor(c/P)+t*z[1]);
    if(H.every(t=>ps.has(on(t,u))&&ps.has(on(t,v))))return true;
  }
  return false;
}
for(const [d,c,n,m,nodes,completions] of cases){
  const r=check(d,c,n);
  checkEq(r.masks,m); checkEq(r.completions,completions);
  if(nodes!==null)checkEq(r.nodes,nodes);
  if(completions)for(const A of r.sets)if(!binaryCross(A))throw Error("non-cross");
  delete r.sets; console.log(r);
}
// In the reference direction mask, only the two axes normalize the remaining
// directions to a multiplicative coset of Hstar.
const mask=[0,4,10,12,13], axisPairs=[];
const vec=s=>s===P?[0,1]:[1,s],det=(u,v)=>mod(u[0]*v[1]-u[1]*v[0]);
for(let i=0;i<mask.length;i++)for(let j=i+1;j<mask.length;j++){
  const a=vec(mask[i]),b=vec(mask[j]);
  const R=mask.filter((_,k)=>k!==i&&k!==j).map(s=>mod(det(vec(s),a)*inv[det(vec(s),b)]));
  if(R.every(z=>Hstar.includes(mod(z*inv[R[0]]))))axisPairs.push([mask[i],mask[j]]);
}
checkEq(JSON.stringify(axisPairs),"[[0,13]]");
checkEq(new Set(H.flatMap(a=>H.map(b=>mod(a-b)))).size,13);

// For thirteen points with <=10 directions there are two missing directions.
// Normalize them to horizontal and vertical, so the points form a permutation
// graph; normalize graph values f(0)=0 and f(1)=1.
function graphCheck() {
 const slopes=Array.from({length:P},(_,i)=>Array.from({length:P},(_,j)=>
   Array.from({length:P},(_,u)=>Array.from({length:P},(_,v)=>mod((u-v)*inv[mod(i-j)])))));
 const f=[0,1],G=new Uint8Array(P*P);
 for(let i=0;i<2;i++)for(let s=0;s<P;s++)++G[s*P+mod(i-s*i)];
 let nodes=0,sols=0;
 function dfs(r,used,ds,n){
   ++nodes;
   if(r===P){++sols;return;}
   for(let y=0;y<P;y++){
     if(used&(1<<y))continue;
     let dd=ds,nn=n,good=true;
     for(let i=0;i<r;i++){
       const s=slopes[r][i][y][f[i]],bit=1<<s;
       if(G[s*P+mod(y-s*r)]===4){good=false;break;}
       if(!(dd&bit)){dd|=bit;nn++;if(nn>10){good=false;break;}}
     }
     if(!good)continue;
     f.push(y);for(let s=0;s<P;s++)++G[s*P+mod(y-s*r)];
     dfs(r+1,used|(1<<y),dd,nn);
     f.pop();for(let s=0;s<P;s++)--G[s*P+mod(y-s*r)];
   }
 }
 dfs(2,3,1<<1,1);return {nodes,sols};
}
const g=graphCheck();checkEq(g.sols,0);checkEq(g.nodes,98331);console.log(g);
let cubicSmall=0;
for(let a=0;a<P;a++)for(let b=0;b<P;b++)for(let c=0;c<P;c++)for(let d=0;d<P;d++){
  let sum=0,cap=0;
  for(let t=0;t<P;t++){const z=mod(a+t*(b+t*(c+t*d)));sum+=z;cap=Math.max(cap,z);}
  if(sum===91&&cap<=9){++cubicSmall;if(a!==7||b||c||d)throw Error("bad cubic");}
}
checkEq(cubicSmall,1);console.log({cubicSmall});
