// Verify length-17 Cartan-free B-fixed border-apolar elimination for M3.
// Node.js, no packages. Integer union-find, exact F_101 row reductions.
'use strict';
const root=[[0,1],[0,2],[1,2]];
const pts=[];for(let i=0;i<3;i++)for(let k=0;k<3;k++)for(let r=0;r<3;r++)pts.push([i,k,...root[r]]);
const idx=(i,k,r)=>((i*3+k)*3+r);
function prereq([i,k,r,c]){
 let a=[];if(i>0)a.push(idx(i-1,k,root.findIndex(x=>x[0]===r&&x[1]===c)));
 if(k<2)a.push(idx(i,k+1,root.findIndex(x=>x[0]===r&&x[1]===c)));
 if(r===0&&c===1||r===1&&c===2)a.push(idx(i,k,1));
 return a;
}
const depot=pts.map(prereq);
let order=[],done=new Set();while(order.length<pts.length){let x=depot.findIndex((d,i)=>!done.has(i)&&d.every(v=>done.has(v)));if(x<0)throw Error();done.add(x);order.push(x);}
function enums(n){let out=[];function go(k,S){if(S.length===n){out.push(S.reduce((m,b)=>m|(1<<b),0));return;}if(order.length-k<n-S.length)return;const id=order[k];if(depot[id].every(t=>S.includes(t)))go(k+1,[...S,id]);go(k+1,S);}go(0,[]);return out;}
function ds(n){let a=Array.from({length:n},(_,i)=>i);function f(x){while(a[x]!==x)x=a[x]=a[a[x]];return x;}return {u:(i,j)=>{a[f(i)]=f(j)},dim:()=>new Set(a.map((_,i)=>f(i))).size-1};}
function impose(mask,get,D,Z){
 for(let i=0;i<3;i++)for(let k=0;k<3;k++){for(let j=1;j<3;j++)D.u(get(i*3,k),get(i*3+j,j*3+k));
 for(let j=0;j<3;j++)for(let l=0;l<3;l++)if(j!==l){const r=root.findIndex(x=>x[0]===l&&x[1]===j);if(r<0||!(mask&(1<<idx(i,k,r))))D.u(Z,get(i*3+j,l*3+k));}}
}

const ix=(a,b,c)=>81*a+9*b+c;
function pair(mask,side){
 const d=ds(730),z=729;
 for(let j=0;j<9;j++)impose(mask,(a,b)=>side===0?ix(a,j,b):ix(a,b,j),d,z);
 for(let a=0;a<9;a++)for(let b=0;b<9;b++)for(let c=0;c<9;c++)d.u(ix(a,b,c),side===0?ix(b,a,c):ix(a,c,b));
 return d.dim();
}
function triple(A,B,C){
 const d=ds(730),z=729;
 for(let j=0;j<9;j++){impose(A,(a,b)=>ix(a,b,j),d,z);impose(B,(a,b)=>ix(j,a,b),d,z);impose(C,(a,b)=>ix(b,j,a),d,z);}
 return d.dim();
}
function rankSparse(cols,dim,P=101){
 const piv=Array(dim),inv=Array(P).fill(0);inv[1]=1;for(let i=2;i<P;i++)inv[i]=(P-Math.floor(P/i)*inv[P%i]%P)%P;
 let rank=0;
 for(let inp of cols){
  let m=new Map();
  for(let [k,w] of inp){let v=((m.get(k)||0)+w+P)%P;if(v)m.set(k,v);else m.delete(k);}
  while(m.size){
   let a=Math.min(...m.keys()),c=m.get(a);if(!piv[a]){
    for(let [k,v] of m)m.set(k,v*inv[c]%P);piv[a]=m;rank++;break;
   }
   for(let [k,v] of piv[a]){const s=((m.get(k)||0)-c*v)%P;if(s)m.set(k,(s+P)%P);else m.delete(k);}
  }
 }
 return rank;
}
function sq(mask){
 let es=[];for(let i=0;i<3;i++)for(let k=0;k<3;k++)es.push(Array.from({length:3},(_,j)=>[3*i+j,3*j+k]));
 pts.forEach(([i,k,l,j],a)=>{if((mask>>a)&1)es.push([[3*i+j,3*l+k]]);});
 const wx=(a,b)=>a>b?wx(b,a):b*(b-1)/2+a, cols=[];
 for(let e of es)for(let a=0;a<9;a++)for(let b=0;b<9;b++)cols.push(e.flatMap(([i,j])=>i===a||j===b?[]:[[36*wx(i,a)+wx(j,b),(i<a)===(j<b)?1:-1]]));
 let rank=rankSparse(cols,1296);return {mask,rank,codim:17*81-rank-136,pass:rank<=952};
}

const assert=(x,msg)=>{if(!x)throw Error(msg);};
const all=enums(8);
assert(all.length===82,'enumeration');
const pairs=all.filter(x=>pair(x,0)>=17&&pair(x,1)>=17);
assert(pairs.length===14,'pair prolongation');
const cubic=[];
for(const a of pairs)for(const b of pairs)for(const c of pairs){const d=triple(a,b,c);if(d>=17)cubic.push({a,b,c,d});}
const hist={};for(const o of cubic)hist[o.d]=(hist[o.d]??0)+1;
assert(cubic.length===37 && hist[17]===27 && hist[18]===9 && hist[19]===1,'triple prolongation');
const sqs=pairs.map(sq), provisional=sqs.filter(p=>p.pass).map(o=>o.mask);
assert(provisional.join(',')==='110808,221616','modular square exclusions');
const last=[];
for(const a of provisional)for(const b of provisional)for(const c of provisional)last.push(triple(a,b,c));
assert(last.length===8 && last.every(d=>d===9),'all remaining triples must fail over every field');
console.log(JSON.stringify({candidates:all.length,pairProlongations:pairs.length,cubicProlongations:hist,squareRanks:sqs,remainingTripleDimensions:last},null,2));
