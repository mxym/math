'use strict';
const p=17,R=Array.from({length:p},(_,i)=>i),mod=x=>(x%p+p)%p,inv=R.map(a=>R.find(b=>mod(a*b)===1));
function normalizedLevels(m){
 const already=new Uint8Array(1<<p),yes=[];
 function go(q,X,mask){
  if(X.length<m){for(let z=q;z<=p-(m-X.length);z++)go(z+1,[...X,z],mask|(1<<z));return;}
  if(already[mask])return;
  yes.push(X);
  for(let a=1;a<p;a++)for(let b of R){let m2=0;for(const x of X)m2|=1<<mod(a*x+b);already[m2]=1;}
 }
 go(0,[],0);return yes;
}
function lam(S){return S.map(x=>inv[S.reduce((d,y)=>x===y?d:mod(d*(x-y)),1)]);}
function basis(A){
 return A.map(i=>{
  let C=[1],den=1;
  for(const z of A)if(i!==z){let D=Array(C.length+1).fill(0);for(let j=0;j<C.length;j++){D[j]=mod(D[j]-z*C[j]);D[j+1]=mod(D[j+1]+C[j]);}C=D;den=mod(den*(i-z));}
  return C.map(x=>mod(x*inv[den]));
 });
}
function many(m,h,cap){
 const lev=normalizedLevels(m), lamTab=lev.map(lam), raw=lev.map((Y,i)=>{
  const L=lamTab[i],A=basis(Y.slice(0,h+1)),C=Y.map((y,i)=>A.map((f,j)=>mod(L[i]*inv[L[j]]*f.reduceRight((s,v)=>mod(s*y+v),0))));
  const T=[],rows=[];
  function choose(j,S){
    if(j<=h){for(let v=0;v<=Math.min(cap,17-S);v++){T.push(v);choose(j+1,S+v);T.pop();}return;}
    const row=T.slice();
    for(let x=h+1;x<m;x++){const v=mod(T.reduce((s,v,j)=>s+v*C[x][j],0));S+=v;if(v>cap||S>17)return;row.push(v);}
    if(S!==17)return;
    const coeff=R.slice(0,h+1).map(k=>mod(T.reduce((s,v,j)=>s+v*inv[L[j]]*A[j][k],0)));
    rows.push({row,coeff});
  }
  choose(0,0);
  return {count:rows.length,indexed:Array.from({length:h+2},(_,fixed)=>{
    const z=new Map();
    for(const e of rows){
      let k=0;for(let j=h;j>h-fixed;j--)k=k*p+e.coeff[j];
      if(!z.has(k))z.set(k,[]);z.get(k).push(e);
    }
    return z;
  })};
 });
 const depth=Array(m+1).fill(0),result=[];
 for(let nx=0;nx<lev.length;nx++){
  const X=lev[nx],L=lamTab[nx], interpol=X.map((t,i)=>R.slice(0,h+1).map(d=> (i<=d?[]:X.slice(0,d+1).map((v,j)=>{
    let q=1;for(const u of X.slice(0,d+1))if(u!==v)q=mod(q*(t-u)*inv[mod(v-u)]);return mod(q*L[i]*inv[L[j]]);
  }))));
  for(let ny=nx;ny<lev.length;ny++){
   const tab=raw[ny].indexed, seq=[], cols=Array(m).fill(0);
   function go(i){
    depth[i]++;
    if(i===m){if(cols.every(x=>x===17))result.push({X,Y:lev[ny],rows:seq.map(q=>q.row)});return;}
    let key=0;
    for(let j=h;j>=Math.max(0,h+1-i);j--){const D=interpol[i][h-j];key=key*p+mod(D.reduce((s,u,k)=>s+u*seq[k].coeff[j],0));}
    for(const e of tab[Math.min(i,h+1)].get(key)??[]){
     if(e.row.some((v,j)=>v+cols[j]>17))continue;
     for(let j=0;j<m;j++)cols[j]+=e.row[j];seq.push(e);go(i+1);seq.pop();for(let j=0;j<m;j++)cols[j]-=e.row[j];
    }
   }
   go(0);
  }
 }
 return {m,h,cap,classes:lev.length,minRows:Math.min(...raw.map(x=>x.count)),maxRows:Math.max(...raw.map(x=>x.count)),depth,count:result.length,result};
}

const all=many(5,2,5), H={},valid=[];
for(const v of all.result){let mx=0, U=0, M=[];
 for(let s=0;s<=17;s++){const a=Array(17).fill(0);
  for(let i=0;i<5;i++)for(let j=0;j<5;j++)a[s===17?v.Y[j]:mod(v.X[i]+s*v.Y[j])]+=v.rows[i][j];
  mx=Math.max(mx,...a);if(a.every(x=>x===5)){U++;M.push(s);}
 }
 const k=[mx,U].join();H[k]=(H[k]??0)+1;if(mx<=17&&U>0)valid.push({v,U,M,mx});
}
if(all.classes!==25||all.count!==45||all.depth.join()!=='325,8104,11913,1426,63,45'||valid.length)throw Error('grid or orbit census');
console.log({classes:all.classes,depth:all.depth,count:all.count,H,valid});

