// Run with Node.js: node verify.js. This checks small lengths, not the all-length theorem.
"use strict";
const mod=251;
const eps=(i,j,k)=>i===j||j===k||i===k?0:(j-i+3)%3===1?1:-1;
function sector(s,t){
 const shift=w=>{const v=w.at(-1);return [v,...w.slice(0,-1)]},mu=(-1)**(s+1),wlist=[],map=new Map,seen=new Set();
 for(let n=0;n<3**s;n++){
  let a=n,w=[];for(let j=0;j<s;j++){w.push(a%3);a=a/3|0}
  if(w.reduce((z,i)=>z*t[i],1)!==1||seen.has(w.join("")))continue;
  let v=w,c=1,o=[];
  do{let k=v.join("");o.push([k,c]);seen.add(k);c*=mu*t[v.at(-1)];v=shift(v);}while(v.join("")!==w.join(""));
  if(c!==1)continue;for(const [k,c] of o)map.set(k,[wlist.length,c]);wlist.push(w);
 }
 return {s,t,mu,wlist,map,shift};
}
function mat(A,B,lambda) {
 return A.wlist.map(w0=>{let r=Array(B.wlist.length).fill(0),w=w0,c=1;
  for(let j=0;j<A.s;j++){for(let k=0;k<3;k++)for(let l=0;l<3;l++){
    let z=eps(k,l,w[0])*lambda[w[0]];
    if(!z)continue;let e=B.map.get([k,l,...w.slice(1)].join(""));
    if(e)r[e[0]]+=z*c*e[1];
  }c*=A.mu*A.t[w.at(-1)];w=A.shift(w);}return r;});
}
function rank(a){a=a.map(r=>r.map(x=>(x%mod+mod)%mod));let k=0;for(let j=0;j<(a[0]?.length??0)&&k<a.length;j++){let i=a.findIndex((r,i)=>i>=k&&r[j]);if(i<0)continue;[a[i],a[k]]=[a[k],a[i]];let v=1;while(v*a[k][j]%mod!==1)v++;for(let i=k+1;i<a.length;i++){let f=v*a[i][j]%mod;if(f)for(let l=j;l<a[i].length;l++)a[i][l]=(a[i][l]+mod*mod-f*a[k][l])%mod}k++}return k}
for(const lambda of [[1,1,1],[2,0,1],[0,0,1]]) for(const t of [[1,1,1],[-1,-1,1]]){
 let prev=0,res=[];for(let s=1;s<=7;s++){let a=sector(s,t),b=sector(s+1,t),r=rank(mat(a,b,lambda));res.push(a.wlist.length-prev-r);prev=r;}const s0=lambda[1]===1, light=lambda[0]===2,twist=t[0]===-1;const ex=Array.from({length:7},(_,j)=>{let s=j+1;return s0?(twist?1:0):light?1:(s%2===Number(!twist)?s+1:s);});if(res.some((v,j)=>v!==ex[j]))throw Error(JSON.stringify([lambda,t,res,ex]));process.stdout.write(JSON.stringify({lambda,twist,cohomology:res})+'\n');
}