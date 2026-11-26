'use strict';
// Characteristic-zero certificate through degree 4 and quintic squares.
const out=console.log;


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
const hv=(h,t)=>({K12:[-2,1,1],K01:[1,1,-2],H01:[1,-1,0],H12:[0,1,-1],free:t===null?[0,1,-1]:[1,t,-1-t]})[h];
const roots=[[0,1],[0,2],[1,2]];
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
const sx=(a,b)=>a>b?sx(b,a):b*(b+1)/2+a;

const rc=[[0,0],[0,1],[0,2],[1,1],[1,2],[2,2]];
const pp=rc.flatMap(row=>rc.slice().reverse().map(col=>({row,col,m:row[0]===row[1]||col[0]===col[1]?1:2})));
const findPure=(r,c)=>pp.findIndex(x=>''+x.row===''+r&&''+x.col===''+c);
const records=pp.map((x,i)=>{
 const P=[];
 for(let k=0;k<2;k++){
  if(x.row[k]>0){let z=x.row.slice();z[k]--;z.sort();P.push(findPure(z,x.col));}
  if(x.col[k]<2){let z=x.col.slice();z[k]++;z.sort();P.push(findPure(x.row,z));}
 }
 return [...new Set(P)];
});
if(records.some((L,j)=>L.some(i=>i>=j||i<0)))throw Error("order");
const dims=[0,1,1,1,2]; // 0,S,W,F,SW
function pureIdeal(L){
 let out=[];
 for(let [t,{row:[i,k],col:[j,l],m}] of pp.entries()){
  let a=i*3+j,b=k*3+l,c=i*3+l,d=k*3+j;
  if(m===1){if(!L[t])out.push([[a,b,1]]);continue;}
  if(!L[t])out.push([[a,b,1]],[[c,d,1]]);
  if(L[t]===1)out.push([[a,b,1],[c,d,-1]]);
  if(L[t]===2)out.push([[a,b,1],[c,d,+1]]);
 }
 return out;
}

function makeSym(d){
 const m=[];
 function go(a,j){if(a.length===d){m.push(a);return;}for(let i=j;i<9;i++)go([...a,i],i);}
 go([],0);const ix=new Map(m.map((a,i)=>[a.join(','),i]));
 return {m,ind:a=>ix.get([...a].sort((a,b)=>a-b).join(','))};
}
const s3=makeSym(3),s4=makeSym(4);
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a;}

function rankQ(cols,n){
 const piv=Array(n);
 let rank=0;
 function prim(v) {
  let g=0n;
  for(let x of v.values()){g=gcd(g,x);if(g===1n)return;}
  if(g>1n)for(let [k,x] of v)v.set(k,x/g);
 }
 for(let col of cols){
  const v=new Map;
  function add(k,u){const s=(v.get(k)||0n)+u;if(s)v.set(k,s);else v.delete(k);}
  for(let [k,x] of col)add(k,BigInt(x));
  while(v.size){
   const p=Math.min(...v.keys()),f=v.get(p);
   if(!piv[p]){prim(v);piv[p]=v;rank++;break;}
   const q=piv[p],h=q.get(p);
   if(h!==1n)for(let [k,w] of v)v.set(k,w*h);
   for(let [k,x] of q)add(k,-f*x);
   prim(v);
  }
 }
 return rank;
}

const W=[
 [1,1,1,0,0,0,1,4,1,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,1,0,0,0,0,0],
 [1,1,1,1,0,0,1,4,1,1,0,0,1,4,1,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
 [1,1,0,1,0,0,1,4,0,4,0,0,1,4,0,4,0,0,1,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0]
];
const ids=[11,196,29];
const Q=W.map(pureIdeal);
for(let g of W)if(g.reduce((a,x)=>a+dims[x],0)!==17)throw Error("pure dimension");
for(let slot of [0,1,2]){
 let d=0;
 for(let [i,{row,col}] of pp.entries()){
  if(slot===0&&row[1]<=1&&col[0]>=1||slot===1&&row[1]===0&&col[0]>=1||slot===2&&row[1]<=1&&col[0]===2)d+=dims[W[slot][i]];
 }
 if(d<(slot===0?5:3))throw Error("box intersection");
}
for(let P of Q){
 const gs=P.map(c=>c.map(([a,b,w])=>[sx(a,b),w]));
 if(rankQ(gs,45)!==28)throw Error("quadratic ideal dimension");
 for(let side=0;side<2;side++)for(let root=0;root<2;root++){
  const act=u=>{
   let i=Math.floor(u/3),j=u%3;
   if(side===0&&i===root)return [u+3,-1]; // dual of row factor
   if(side===1&&j===root+1)return [u-1,1];
   return null;
  };
  const ds=P.map(g=>g.flatMap(([a,b,w])=>{
   let c=act(a),d=act(b),r=[];
   if(c)r.push([sx(c[0],b),w*c[1]]);
   if(d)r.push([sx(a,d[0]),w*d[1]]);
   return r;
  }));
  if(rankQ(gs.concat(ds),45)!==28)throw Error("pure Borel instability");
 }
}
const sym=[makeSym(0),makeSym(1),makeSym(2),s3,s4];
function term(a,b,j,k){
 const t=[[],[],[]]; t[j].push(a);t[k].push(b); return t;
}
const atoms=[];
for(let j=0;j<3;j++){
 const g0=[0,0,0],g1=[0,0,0], k=(j+1)%3;
 g0[j]=2;g1[j]=1;g1[k]=1;
 atoms.push([g0,Q[j].map(c=>c.map(([a,b,w])=>[term(a,b,j,j),w]))]);
 atoms.push([g1,dat(st[ids[j]],0).F.map(c=>c.map(([a,b,w])=>[term(a,b,j,k),w]))]);
}
function degree3(v){return v[0]+v[1]+v[2];}
function mult(d){
 const ss=d.map(i=>sym[i]), dim=ss.reduce((a,s)=>a*s.m.length,1);
 const index=v=>(ss[0].ind(v[0])*ss[1].m.length+ss[1].ind(v[1]))*ss[2].m.length+ss[2].ind(v[2]);
 const append=(a,b)=>a.map((t,i)=>t.concat(b[i]));
 return {ss,dim,index,append};
}
function simpleCols(d){
 const {ss,dim,index,append}=mult(d), cols=[];
 for(let [g,F] of atoms){
  const D=d.map((x,i)=>x-g[i]);if(D.some(x=>x<0))continue;
  const us=sym[D[0]].m,vs=sym[D[1]].m,ws=sym[D[2]].m;
  for(let c of F)for(let u of us)for(let v of vs)for(let w of ws)cols.push(c.map(([a,x])=>[index(append(a,[u,v,w])),x]));
 }
 return {cols,dim};
}
function sqCols(d){
 const {dim,index,append}=mult(d), cols=[];
 for(let i=0;i<atoms.length;i++)for(let j=i;j<atoms.length;j++){
  const [g,F]=atoms[i],[h,G]=atoms[j];
  if(g.some((a,l)=>a+h[l]!==d[l]))continue;
  for(let a=0;a<F.length;a++)for(let b=(i===j?a:0);b<G.length;b++)
   cols.push(F[a].flatMap(([u,x])=>G[b].map(([v,y])=>[index(append(u,v)),x*y])));
 }
 return {cols,dim};
}
function sh(d,square){
 const {cols,dim}=(square?sqCols:simpleCols)(d);
 return dim-rankQ(cols,dim);
}
const list=[];for(let i=0;i<=4;i++)for(let j=0;j<=4-i;j++)for(let k=0;k<=4-i-j;k++)if(i+j+k>=3)list.push([i,j,k]);
const H=[],S=[];
for(let d of list){
 let h=sh(d,false); H.push([d.join(''),h]);
 if(d.join('')==='111'?h!==17:h<17)throw Error("ordinary Hilbert test "+d);
 if(degree3(d)===4){
  const bound=d.filter(x=>x>0).length===3?425:d.filter(x=>x>0).length===2?289:153;
  let sq=sh(d,true);S.push([d.join(''),sq]); if(sq<bound)throw Error("square Hilbert test "+d);
 }
}
out({ordinary:H,square:S});

const ext={
 '003':[[[],[],[0,5,8]],[[],[],[1,5,8]],[[],[],[0,2,8]],[[],[],[1,2,8]],[[],[],[5,5,8]],[[],[],[3,5,5]],[[],[],[4,5,5]],[[],[],[2,5,8]]],
 '012':[],
 '021':[[[],[2,5],[8]]],
 '030':[[[],[4,4,4],[]],[[],[3,5,5],[]],[[],[4,4,5],[]],[[],[4,5,5],[]],[[],[5,5,5],[]],[[],[0,5,5],[]],[[],[1,4,4],[]],[[],[1,4,5],[]],[[],[2,4,4],[]],[[],[1,5,5],[]],[[],[2,4,5],[]],[[],[2,5,5],[]],[[],[1,1,7],[]]],
 '102':[[[7],[],[5,5]]],
 '111':[],
 '120':[[[5],[1,7],[]]],
 '201':[[[4,4],[],[5]],[[4,5],[],[5]],[[5,5],[],[5]]],
 '210':[[[4,4],[1],[]],[[4,4],[2],[]],[[4,5],[1],[]]],
 '300':[[[8,8,8],[],[]],[[5,8,8],[],[]],[[2,8,8],[],[]],[[4,4,7],[],[]],[[4,4,8],[],[]],[[4,5,8],[],[]],[[1,4,7],[],[]],[[5,5,8],[],[]],[[1,4,8],[],[]],[[1,5,8],[],[]],[[1,1,7],[],[]],[[2,5,8],[],[]],[[1,1,8],[],[]],[[1,2,8],[],[]],[[2,2,8],[],[]],[[4,4,4],[],[]],[[4,4,5],[],[]],[[4,5,5],[],[]]]
};
const R=[];
for(let d of list){
 const {cols,dim}=simpleCols(d), {index,append}=mult(d), ex=[];
 if(degree3(d)===3) ex.push(...ext[d.join('')]);
 else for(let i=0;i<3;i++){
  if(!d[i])continue;
  const g=d.map((a,j)=>i===j?a-1:a);
  for(let m of ext[g.join('')])for(let x=0;x<9;x++){
   const n=[[],[],[]];n[i].push(x);ex.push(append(m,n));
  }
 }
 const h=dim-rankQ(cols.concat(ex.map(m=>[[index(m),1]])),dim);
 if(degree3(d)===3?h!==17:h<17)throw Error("weak extension fails "+d);
 R.push([d.join(''),h]);
}
out({weakExtension:R});

sym.push(makeSym(5));
function deg3terms(d,extras){
 const cs=[];
 const append=(a,b)=>a.map((u,i)=>u.concat(b[i]));
 for(let [g,F] of atoms)for(let i=0;i<3;i++){
  if(d.some((x,j)=>x!==g[j]+(i===j?1:0)))continue;
  for(let a=0;a<9;a++){
   const q=[[],[],[]];q[i].push(a);
   for(let g of F)cs.push(g.map(([u,v])=>[append(u,q),v]));
  }
 }
 const ex=extras.find(([a])=>''+a===''+d)?.[1]??[];
 for(let q of ex)cs.push([[q,1]]);
 return cs;
}
function s5(extras){
 const out5=[];
 for(let a=0;a<=5;a++)for(let b=0;b<=5-a;b++){
  const d=[a,b,5-a-b], {index,append,dim}=mult(d), C=[];
  for(let [g,F] of atoms){
   const e=d.map((v,i)=>v-g[i]);
   if(e.some(j=>j<0))continue;
   const G=deg3terms(e,extras);
   for(let f of F)for(let g of G)C.push(f.flatMap(([u,v])=>g.map(([x,y])=>[index(append(u,x)),v*y])));
  }
  const r=dim-rankQ(C,dim);
  out5.push([d.join(''),r]);
 }
 out(out5);
 return out5;
}

const got=s5(Object.entries(ext).map(([s,m])=>[s.split('').map(Number),m]));
const exp=[251,424,349,388,368,219,412,553,533,516,379,364,601,600,364,398,636,392,398,395,221];
if(got.length!==exp.length||got.some(([s,q],i)=>{
 const w=s.split('').filter(x=>x!=='0').length;
 return q!==exp[i]||q<(w===3?425:w===2?289:153);
}))throw Error("quintic square tests");
