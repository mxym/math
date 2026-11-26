'use strict';
// Necessary (210),(120),(220)-square,(111) classification for length 17 at M3.
const out=console.log;
// Exact polynomial certificates and modular rank lower bounds, not an unrestricted rank certificate.
// Both root masks use (01,02,12); the negative mask means the transpose root.


const Ts=[];
function T(p,n,h,dim){Ts.push({p,n,h,dim,size:((p&1)>0)+((p&2)>0)+((p&4)>0)+((n&1)>0)+((n&2)>0)+((n&4)>0)+dim});}
for(let p of [0,2,3,6,7])T(p,0,'none',0);
T(3,0,'K12',1);T(6,0,'K01',1);T(7,0,'free',1);
T(7,1,'H01',1);T(7,4,'H12',1);
for(let n of [0,1,4,5,7])T(7,n,'full',2);
const grid=[];for(let i=0;i<3;i++)for(let k=2;k>=0;k--)grid.push([i,k]);
function stacks(N){
 let out=[];function go(j,ts,left,param){
  if(j===9){if(left===0)out.push({ts,param});return;}
  const [i,k]=grid[j];const parents=[];
  if(i>0)parents.push(ts[j-3]);if(k<2)parents.push(ts[j-1]);
  for(let t of Ts){if(t.size>left)continue;
   let z=param,ok=true;
   for(let f of parents){
    if((t.p&~f.p)!==0||(t.n&~f.n)!==0||t.dim>f.dim){ok=false;break;}
    if(t.dim===1&&f.dim===1&&t.h!==f.h){
      if(t.h!=='free'&&f.h!=='free'){ok=false;break;}
      let c=t.h==='free'?f.h:t.h;if(z&&z!==c){ok=false;break;}z=c;
    }
   }
   if(ok)go(j+1,[...ts,t],left-t.size,z);
  }
 }
 go(0,[],N,null);return out;
}
const st=stacks(8);
function rankSparse(cols,dim,P=101){
 const piv=Array(dim),inv=Array(P).fill(0);inv[1]=1;for(let i=2;i<P;i++)inv[i]=(P-Math.floor(P/i)*inv[P%i]%P)%P;
 let rank=0;
 for(let inp of cols){
  let m=new Map();
  for(let [k,w] of inp){let v=(((m.get(k)||0)+w)%P+P)%P;if(v)m.set(k,v);else m.delete(k);}
  while(m.size){
   let a=Math.min(...m.keys()),c=m.get(a);if(!piv[a]){
    for(let [k,v] of m)m.set(k,v*inv[c]%P);piv[a]=m;rank++;break;
   }
   for(let [k,v] of piv[a]){const s=((m.get(k)||0)-c*v)%P;if(s)m.set(k,(s+P)%P);else m.delete(k);}
  }
 }
 return rank;
}

const hv=(h,t)=>({K12:[-2,1,1],K01:[1,1,-2],H01:[1,-1,0],H12:[0,1,-1],free:t===null?[0,1,-1]:[1,t,-1-t]})[h];
const P=101, norm=x=>(x%P+P)%P, roots=[[0,1],[0,2],[1,2]];
function dat(o,t){
 const E=[],F=[];
 for(let k0=0;k0<9;k0++){
  const [i,k]=grid[k0],a=o.ts[k0];
  let ds=Array.from({length:3},(_,j)=>[3*i+j,3*j+k,1]);E.push(ds);
  if(a.dim===0){F.push([ds[0],[...ds[1].slice(0,2),-1]],[ds[0],[...ds[2].slice(0,2),-1]]);}
  if(a.dim===1){let h=hv(a.h==='free'?(o.param??'free'):a.h,t);
   E.push(ds.map(([x,y],j)=>[x,y,h[j]]));
   F.push(ds.map(([x,y],j)=>[x,y,h[(j+1)%3]-h[(j+2)%3]]));
  }
  if(a.dim===2){E.push([ds[0],[...ds[1].slice(0,2),-1]],[ds[1],[...ds[2].slice(0,2),-1]]);}
  for(let j=0;j<3;j++)for(let l=0;l<3;l++)if(j!==l){
   let r=roots.findIndex(([x,y])=>x===Math.min(l,j)&&y===Math.max(l,j));
   let dest=((1<<r)&(l<j?a.p:a.n))?E:F;dest.push([[i*3+j,l*3+k,1]]);
  }
 }
 return {E,F};
}
function getPairRank(f,side){
 const ix=(a,b)=>{if(a>b)[a,b]=[b,a];return b*(b+1)/2+a;};let cols=[];
 for(let s of f)for(let j=0;j<9;j++)cols.push(s.map(([a,b,w])=>[side===0?ix(a,j)*9+b:a*45+ix(b,j),w]));
 return rankSparse(cols,405);
}
function getSquareRank(e){
 const ix=(a,b)=>a>b?ix(b,a):b*(b-1)/2+a;let cols=[];
 for(let s of e)for(let a=0;a<9;a++)for(let b=0;b<9;b++)cols.push(s.flatMap(([i,j,w])=>i===a||j===b?[]:[[36*ix(i,a)+ix(j,b),(i<a)===(j<b)?w:-w]]));
 return rankSparse(cols,1296);
}
function screen(o,t){const {E,F}=dat(o,t);return getPairRank(F,0)<=388 && getPairRank(F,1)<=388 && getSquareRank(E)<=952;}

const weights=Array.from({length:9},(_,i)=>17**i);
const ww=Array.from({length:3},(_,f)=>Array.from({length:9},(_,i)=>weights[f*3+Math.floor(i/3)]-weights[((f+1)%3)*3+i%3]));
const sPairs=Array.from({length:9},(_,j)=>Array.from({length:j+1},(_,i)=>[i,j])).flat();
const aPairs=sPairs.filter(([i,j])=>i!==j);
const Ax=ww[0],Bx=ww[1];
const rw=[
 sPairs.flatMap(([i,j])=>Bx.map(b=>Ax[i]+Ax[j]+b)),
 Ax.flatMap(a=>sPairs.map(([i,j])=>a+Bx[i]+Bx[j])),
 aPairs.flatMap(([i,j])=>aPairs.map(([k,l])=>Ax[i]+Ax[j]+Bx[k]+Bx[l]))
];
const sx=(a,b)=>a>b?sx(b,a):b*(b+1)/2+a;
const wx=(a,b)=>a>b?wx(b,a):b*(b-1)/2+a;
function cols(o,t,kind){
 const {E,F}=dat(o,t);const out=[];
 if(kind<2){
  for(let s of F)for(let j=0;j<9;j++)out.push(s.map(([a,b,w])=>[kind===0?sx(a,j)*9+b:a*45+sx(b,j),w]));
 }else{
  for(let s of E)for(let a=0;a<9;a++)for(let b=0;b<9;b++)out.push(s.flatMap(([i,j,w])=>i===a||j===b?[]:[[36*wx(i,a)+wx(j,b),(i<a)===(j<b)?w:-w]]));
 }
 return out;
}
function getBlocks(o,kind){
 const cs0=cols(o,0,kind),cs1=cols(o,1,kind);
 const M=new Map();
 for(let i of rw[kind].keys()){
  const w=rw[kind][i];
  if(!M.has(w)) M.set(w,{r:[],c:[]});
  M.get(w).r.push(i);
 }
 for(let j=0;j<cs0.length;j++){
  const a=cs0[j],b=cs1[j];if(!a.length)continue;
  const weight=rw[kind][a[0][0]];
  if(!a.every(([k])=>rw[kind][k]===weight))throw Error("weights");
  M.get(weight).c.push(a.map(([k,u],i)=>[k,u,b[i][1]-u]));
 }
 return [...M.values()].filter(v=>v.c.length);
}
function evalBlock({r,c},t){
 const Mm=r.map(()=>new Int32Array(c.length)), ms=new Map(r.map((a,i)=>[a,i]));
 for(let j in c)for(let [i,a,b] of c[j])Mm[ms.get(i)][j]=norm(t===null?b:a+t*b);
 return Mm;
}
function sel(M){
 const r=M.map((_,i)=>i),c=[];let k=0;
 const iP=Array(P).fill(0);iP[1]=1;for(let i=2;i<P;i++)iP[i]=(P-Math.floor(P/i)*iP[P%i]%P)%P;
 for(let j=0;j<M[0].length;j++){
  let z=k;while(z<M.length&&M[z][j]===0)z++;
  if(z===M.length)continue;
  if(z!==k){[M[k],M[z]]=[M[z],M[k]];[r[k],r[z]]=[r[z],r[k]];}
  const p=iP[M[k][j]];for(let i=k+1;i<M.length;i++)if(M[i][j]){
   const f=M[i][j]*p%P;for(let l=j;l<M[i].length;l++)M[i][l]=norm(M[i][l]-f*M[k][l]);
  } c.push(j);k++;
 }
 return {r:r.slice(0,k),c};
}
function minor(B,S){
 const A=Array.from({length:S.r.length},()=>Array.from({length:S.c.length},()=>[0,0])), ix=new Map(S.r.map((j,i)=>[B.r[j],i]));
 for(let [ii,j] of S.c.entries())for(let [k,a,b] of B.c[j])if(ix.has(k))A[ix.get(k)][ii]=[a,b];
 return A;
}
function determinant(M,t) {
 const A=M.map(row=>row.map(([a,b])=>BigInt(a+t*b)));let z=1n,prev=1n;
 for(let k=0;k<A.length-1;k++){
  let j=k;while(j<A.length&&A[j][k]===0n)j++;if(j===A.length)return 0n;
  if(j!==k){[A[j],A[k]]=[A[k],A[j]];z=-z;}
  const p=A[k][k];
  for(let i=k+1;i<A.length;i++)for(let j=k+1;j<A.length;j++){
   A[i][j]=(p*A[i][j]-A[i][k]*A[k][j])/prev;
  }prev=p;
 }
 return A.length?z*A.at(-1).at(-1):1n;
}
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a;}
function primitive(A){while(A.length&&A.at(-1)===0n)A.pop();if(!A.length)return A;const g=A.reduce(gcd,0n)*(A.at(-1)<0n?-1n:1n);return A.map(x=>x/g);}
function poly(M){
 const d=M[0].map((_,j)=>M.some(r=>r[j][1]!==0)).filter(a=>a).length;
 if(!d)return [1n];
 const yy=Array.from({length:d+1},(_,t)=>determinant(M,t)), A=Array(d+1).fill(0n);
 let fac=1n;for(let i=2;i<=d;i++)fac*=BigInt(i);let S=[1n],f=1n;
 for(let k=0;k<=d;k++){
  const z=yy[0]*(fac/f);
  S.forEach((x,i)=>A[i]+=x*z);
  for(let i=0;i<d-k;i++)yy[i]=yy[i+1]-yy[i];
  if(k<d){
   S=[0n,...S].map((a,j)=>a-BigInt(k)*(S[j]??0n));f*=BigInt(k+1);
  }
 }return primitive(A);
}
function blocksFor(o,kind,t=7){
 const B=getBlocks(o,kind);
 return B.map(b=>{
  const s=sel(evalBlock(b,t));
  return {b,s,d:s.r.length,pol:s.r.length?poly(minor(b,s)):[1n]};
 });
}


function splitTest(p){
 for(const [a,b] of [[2n,1n],[1n,2n],[-1n,1n]]){
  while(p.length>1){
   const d=p.length-1,q=Array(d).fill(0n),z=p.slice();
   let K=1n;for(let i=0;i<d;i++)K*=b;
   for(let i=0;i<z.length;i++)z[i]*=K;
   let ok=true;
   for(let i=d;i>0;i--){
    if(z[i]%b){ok=false;break;}q[i-1]=z[i]/b;z[i-1]-=a*q[i-1];
   }
   if(!ok||z[0])break;
   p=primitive(q);
  }
 }
 return p.length===1&&p[0]!==0n;
}
let sp=[1,-2,50,null]; // -1/2 mod F_101 is 50
const plans=[];
let counts={}, free=0;
for(let [i,o] of st.entries()){
 const f=!o.param&&o.ts.some(x=>x.h==='free');
 if(f){
  free++;
  let ok=false;
  for(let [kind,n] of [[0,388],[1,388],[2,952]]){
   const B=blocksFor(o,kind);
   if(B.reduce((a,b)=>a+b.d,0)<=n)continue;
   if(!B.every(({pol})=>splitTest(pol)))throw Error("unseen polynomial "+i);
   ok=true;counts[kind]=(counts[kind]||0)+1;break;
  }
  if(!ok)throw Error("uncertified family "+i);
 }
 for(let t of f?sp:[0])if(screen(o,t))plans.push({i,t,...dat(o,t)});
}
out({free,counts,total:st.length,provisional:plans.map(o=>[o.i,o.t])});

function tripleOps(F,k){
 const ix=(x,y,z)=>81*x+9*y+z, eq=[], rest=[];
 for(let c=0;c<9;c++)for(let col of F){
  const v=col.filter(([, ,w])=>norm(w)!==0).map(([a,b,w])=>[k===0?ix(a,b,c):k===1?ix(c,a,b):ix(b,c,a),w]);
  if(v.length===1)eq.push(v[0][0],729);
  else if(v.length===2&&norm(v[0][1]+v[1][1])===0)eq.push(v[0][0],v[1][0]);
  else if(v.length)rest.push(v);
 }
 return {eq,rest};
}
function cubicTrial(ar){
 const p=Int16Array.from({length:730},(_,i)=>i);
 const find=i=>{while(i!==p[i])i=p[i]=p[p[i]];return i;};
 for(let {eq} of ar)for(let i=0;i<eq.length;i+=2)p[find(eq[i])]=find(eq[i+1]);
 const ids=new Int16Array(730).fill(-1),z=find(729);let d=0;
 for(let i=0;i<729;i++){let k=find(i);if(k!==z&&ids[k]<0)ids[k]=d++;}
 if(d<17)return d;
 const res=ar.flatMap(({rest})=>rest.map(v=>v.flatMap(([k,w])=>{let j=ids[find(k)];return j<0?[]:[[j,w]];})));
 return d-rankSparse(res,d);
}
const ops=plans.map(x=>[0,1,2].map(k=>tripleOps(x.F,k)));
let tri=[];
for(let a=0;a<plans.length;a++)for(let b=a;b<plans.length;b++)for(let c=a;c<plans.length;c++){
 let d=cubicTrial([ops[a][0],ops[b][1],ops[c][2]]);
 if(d>=17)tri.push([a,b,c,d]);
}
out({n:tri.length,triples:tri.map(a=>[...a.slice(0,3).map(i=>[plans[i].i,plans[i].t]),a[3]])});

const expected=[195,196,197,198,200,201,202,203,205,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226];
if(st.length!==227||free!==29||counts[0]!==9||counts[1]!==9||counts[2]!==11||plans.length!==55||tri.length!==expected.length||tri.some(([a,b,c,d],j)=>plans[a].i!==11||plans[b].i!==expected[j]||plans[c].i!==29||plans[a].t!==0||plans[b].t!==0||plans[c].t!==0||d!==17))throw Error('classification mismatch');
