// Node.js. Exact sample checks in F_2521; proofs are not by enumeration.
const P=2521,md=x=>(x%P+P)%P, assert=(b,o)=>{if(!b)throw Error(JSON.stringify(o));};
function pw(x,n){let y=1;n=(n%(P-1)+P-1)%(P-1);while(n){if(n&1)y=md(y*x);x=md(x*x);n>>=1;}return y;}
function rank(M,n){let k=0;for(let j=0;j<n&&k<M.length;j++){let i=k;while(i<M.length&&!M[i][j])i++;if(i===M.length)continue;
 [M[i],M[k]]=[M[k],M[i]];const f=pw(M[k][j],-1);for(let l=j;l<n;l++)M[k][l]=md(f*M[k][l]);
 for(let i=k+1;i<M.length;i++){const c=M[i][j];if(!c)continue;for(let l=j;l<n;l++)M[i][l]=md(M[i][l]-c*M[k][l]);}k++;}return k;}
function basis(n,k,tw,grade,ord){
 const out=[],seen=new Set,idx=new Map(),mu=n%2?1:-1;
 if(n===0)return {out,idx};
 for(let x=0;x<k**n;x++){
  let a=x,w=[];for(let j=0;j<n;j++){w.push(a%k);a=a/k|0;}let g=w.reduce((s,b)=>s+grade(b),0)%ord;
  if(seen.has(w.join("")))continue;
  let v=w,c=1,orb=[];
  do{const p=v.join("");seen.add(p);orb.push([p,c]);
    c=md(c*mu*pw(tw(v.at(-1)),-1));v=[v.at(-1),...v.slice(0,-1)];
  }while(v.join("")!==w.join(""));
  if(c!==1)continue;
  for(const [p,c] of orb)idx.set(p,[out.length,c]);
  out.push([w,g]);
 }
 return {out,idx};
}
function boundary(A,B,prod,tw){
 return A.out.map(([w,g])=>{const r=Array(B.out.length).fill(0);
  for(let j=0;j+1<w.length;j++)for(const [i,c] of prod(w[j],w[j+1])){
   const v=w.slice(0,j).concat(i,w.slice(j+2)),e=B.idx.get(v.join(""));
   if(e)r[e[0]]=md(r[e[0]]+(-1)**j*c*e[1]);
  }
  if(w.length>1)for(const [i,c] of prod(w.at(-1),w[0])){const v=[i,...w.slice(1,-1)],e=B.idx.get(v.join(""));if(e)r[e[0]]=md(r[e[0]]+(-1)**(w.length-1)*tw(w.at(-1))*c*e[1]);}
  return r;});
}
function checkComplex(k,maxN,tw,grade,ord,prod,expect){
 let cases=0;
 for(let n=1;n<=maxN;n++){
  const A=basis(n,k,tw,grade,ord), B=basis(n-1,k,tw,grade,ord), C=basis(n+1,k,tw,grade,ord), D=boundary(A,B,prod,tw), E=boundary(C,A,prod,tw);
  for(let g=0;g<ord;g++){
   const a=A.out.map(([,d],i)=>d===g?i:-1).filter(i=>i>=0);
   const got=a.length-rank(a.map(i=>D[i]),B.out.length)-rank(E.map(r=>a.map(i=>r[i])),a.length);
   assert(got===expect(n,g),[k,n,g,got,expect(n,g)]);cases++;
  }
 }
 return cases;
}
let trig=0, fz=0, tj=0;
for(let d=3;d<=6;d++){
 let eta=2;while(pw(eta,d)!==1||Array.from({length:d-1},(_,i)=>i+1).some(j=>pw(eta,j)===1))eta++;
 for(let a=0;a<d;a++){if(d%2===0&&a%2)continue;
   const u=pw(eta,a),prod=(i,j)=>i+j+2<d?[[i+j+1,1]]:[];
   trig+=checkComplex(d-1,5,i=>pw(u,i+1),i=>i+1,d,prod,(n,w)=>a?(n%2===0&&w===0?1:0):(n%2&&w!==0?1:0));
 }
}
const c=pw(2,-1);
for(const [a,b] of [[1,1],[1,0],[0,1],[2,3]]){
 const prod=(i,j)=>i===j&&i>0?[[0,i===1?a:b]]:
  i===0&&j>0?[[j,j===1?c:-c]]:j===0&&i>0?[[i,i===1?c:-c]]:[];
 fz+=checkComplex(3,6,()=>1,i=>+(i!==0),2,prod,(n,g)=>n%2?(g?2:1):0);
}
// Direct full local Hamiltonians, not cohomology. Letters 0,1 are X,Y; 2 is a hole.
for(const z of [0,1,2,-3])for(const t of [1,-1])for(let n=2;n<=5;n++){
 const a=z-1,b=z+1,c=z*z+1,N=3**n,M=Array.from({length:N},()=>Array(N).fill(0));
 for(let j=0;j<N;j++){
  const w=[];let y=j;for(let i=0;i<n;i++){w.push(y%3);y=y/3|0;}
  for(let i=0;i<n;i++){
   const k=(i+1)%n,u=w[i],v=w[k];let dia=0,off=0;
   if(u===2&&v===2)dia=2*c;else if(u===2||v===2){dia=c;off=-a*b*(i===n-1?t:1);}
   else if(u!==v){dia=u===0?a*a:b*b;off=a*b;}
   M[j][j]=md(M[j][j]+dia);
   if(off){const m=j+(v-u)*3**i+(u-v)*3**k;M[j][m]=md(M[j][m]+off);}
  }
 }
 const got=N-rank(M,N),ex=z?2:n+1+(((-1)**n===t)?n:0);
 assert(got===ex,[z,t,n,got,ex]);tj++;
}
console.log(JSON.stringify({trig,fz,tj}));
