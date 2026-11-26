// Node 18+: node verify.js. Independent modular checks; not the all-length proof.
const assert=(z,msg)=>{if(!z)throw Error(JSON.stringify(msg));};
const p=1009,mod=x=>(x%p+p)%p;
function pow(x,n){if(n<0)return pow(pow(x,p-2),-n);let a=1;while(n){if(n&1)a=mod(a*x);x=mod(x*x);n>>=1;}return a;}
let omega=2;while(pow(omega,3)!==1)omega++;
function sector(n,f){
 const fphase=i=>pow(omega,f*(i-1)),mu=n%2?1:-1,rot=w=>[w.at(-1),...w.slice(0,-1)],seen=new Set,ors=[],map=new Map;
 if(n===0)return {ors,map,n};
 for(let x=0;x<3**n;x++){let z=x,w=[];for(let j=0;j<n;j++){w.push(z%3);z=z/3|0}
  if(f&&w.reduce((s,i)=>s+i-1,0)%3||seen.has(w.join("")))continue;
  let c=1,ys=[],v=w;
  do{const k=v.join("");seen.add(k);ys.push([v,c]);c=mod(c*mu*fphase(v.at(-1)));v=rot(v);}while(v.join("")!==w.join(""));
  if(c!==1)continue;for(const [v,c] of ys)map.set(v.join(""),[ors.length,c]);
  ors.push(ys);
 }return {ors,map,n};
}
function mat(A,B,l,z){
 const rule=[[[2,2,z]],[[0,2,l*z],[2,0,l*z],[1,1,-1]],[[0,0,l]]]; 
 return A.ors.map(o=>{const row=Array(B.ors.length).fill(0),w=o[0][0];for(let j=0;j<w.length;j++)for(const [a,b,c] of rule[w[j]]){
  const v=w.slice(0,j).concat(a,b,w.slice(j+1)), e=B.map.get(v.join(""));if(e)row[e[0]]=mod(row[e[0]]+(-1)**j*c*e[1]);}return row;});
}
function elim(src,n,returnNull=false){
 let M=src.map(r=>r.slice()),i=0,piv=[];
 for(let j=0;j<n&&i<M.length;j++){
  let k=i;while(k<M.length&&!M[k][j])k++;if(k===M.length)continue;
  [M[i],M[k]]=[M[k],M[i]]; const inv=pow(M[i][j],p-2);
  for(let l=j;l<n;l++)M[i][l]=mod(M[i][l]*inv);
  for(let k=returnNull?0:i+1;k<M.length;k++){if(k===i)continue;const f=M[k][j];if(!f)continue;for(let l=j;l<n;l++)M[k][l]=mod(M[k][l]-f*M[i][l]);}
  piv.push(j);i++;
 }
 if(!returnNull)return i;
 const ns=[];const S=new Set(piv);for(let j=0;j<n;j++)if(!S.has(j)){const a=Array(n).fill(0);a[j]=1;for(let k=0;k<piv.length;k++)a[piv[k]]=mod(-M[k][j]);ns.push(a);}return ns;
}
function gcd(a,b){return b?gcd(b,a%b):a;}
function countOrigin(n,f){
 const order=(f?3:1)*n;let z=0;
 for(let j=0;j<order;j++){const g=gcd(n,j);z+=(-1)**((n+1)*j)*(f*(j/g)%3?-1:2)**g;}
 assert(z%order===0,[n,f,z]);return z/order+n%2;
}
let cases=0,checks=0;
for(const lz of [[0,0],[1,0],[0,2],[1,1],[-2,3]])for(let f=0;f<3;f++){
 let prev=0;
 for(let n=1;n<=6;n++){
  const A=sector(n,f),B=sector(n+1,f),[l,z]=lz;
  const rank=elim(mat(A,B,l,z),B.ors.length),got=A.ors.length-prev-rank;
  const exp=!l&&!z?countOrigin(n,f):f?(l&&z?0:1):3*(n%2);
  assert(got===exp,[lz,f,n,got,exp]);cases++;prev=rank;
 }
}
// In untwisted coinvariant coordinates a unit representative equals the orbit
// mean, with metric 1/orbit_length. This fixes the incoming adjoint.
for(const t of [1,2,-3,5])for(const n of [1,3,5]){
 const B=sector(n,0),A=sector(n-1,0),C=sector(n+1,0),out=mat(B,C,t,t),inc=mat(A,B,t,t);
 for(let q=0;q<3;q++){
  const ii=B.ors.map((o,i)=>[i,o[0][0].reduce((s,k)=>s+k-1,0)]).filter(([,s])=>(s%3+3)%3===q).map(([i])=>i);
  const rows=Array.from({length:C.ors.length},(_,j)=>ii.map(i=>out[i][j]));
  rows.push(...inc.map(row=>ii.map(i=>mod(row[i]*pow(B.ors[i].length,-1)))));
  const ns=elim(rows,ii.length,true);assert(ns.length===1,[t,n,q,ns.length]);
  let nn=0,plus=0,minus=0,pure=0;
  ii.forEach((i,j)=>{const o=B.ors[i],nu=o[0][0].filter(x=>x===1).length,c=ns[0][j];nn=mod(nn+c*c*pow(o.length,-1));plus=mod(plus+c*pow(t,nu));minus=mod(minus+c*pow(t,-nu));if(nu===n)pure=c;});
  assert(mod(pow(3,n-1)*nn)===mod(plus*minus),[t,n,q,nn,plus,minus]);checks++;
  if(q===0){assert(plus===mod(pow(3,n-1)*pow(t,n)*pure),[t,n,q,plus,pure]);checks++;}
 }
}
console.log(JSON.stringify({dimensionCases:cases,sumRules:checks}));
