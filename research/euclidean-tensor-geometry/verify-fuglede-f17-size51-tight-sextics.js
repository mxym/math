'use strict';
const p=17,R=Array.from({length:17},(_,i)=>i),mod=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>mod(a*b)===1));
const F=[...R.map(x=>[1,x]),[0,1]],det=([a,b],[c,d])=>mod(a*d-b*c);
const perms=[];
for(let A of F)for(let B of F)for(let C of F)if(A!==B&&A!==C&&B!==C){
 const z=det(C,A)*iv[det(C,B)];
 perms.push(F.map(v=>det(v,A)?mod(det(v,B)*z*iv[det(v,A)]):17));
}
function reps(n){
 const seen=new Uint8Array(1<<18),out=[];
 function go(j,mask,D){
  if(D.length<n){for(let q=j;q<=18-(n-D.length);q++)go(q+1,mask|(1<<q),[...D,q]);return;}
  if(seen[mask])return;
  out.push(D);
  for(const sigma of perms){let m=0;for(let a of D)m|=1<<sigma[a];seen[m]=1;}
 }
 go(0,0,[]);return out;
}

function model(D,d){const n=D.length,r=Math.min(n,d+1),V=Array.from({length:d+1},(_,j)=>D.map(([x,y])=>mod(x**(d-j)*y**j))), A=V.map((a,i)=>a.concat(R.slice(0,d+1).map(j=>+(i===j))));
for(let j=0;j<r;j++){
 let k=A.findIndex((u,i)=>i>=j&&u[j]);if(k<0)throw Error('rank');
 [A[j],A[k]]=[A[k],A[j]];A[j]=A[j].map(v=>mod(v*iv[A[j][j]]));
 for(let k=0;k<=d;k++)if(k!==j){let a=A[k][j];A[k]=A[k].map((v,i)=>mod(v-a*A[j][i]));}
}return {V,A,n,r};}
function solve(M,Y,cb,projective=false){const {A,n,r}=M;const b=A.map(row=>mod(Y.reduce((s,q,j)=>s+q*row[n+j],0)));if(b.slice(r).some(Boolean))return;const a=Array(n).fill(0);
 function go(j,nonzero){if(j===n){if(projective&&!nonzero)return;for(let i=0;i<r;i++){let q=b[i];for(let k=r;k<n;k++)q-=A[i][k]*a[k];a[i]=mod(q);}cb(a);return;}
 for(let x of R){if(projective&&!nonzero&&x>1)break;a[j]=x;go(j+1,nonzero||x>0);}
 }go(r,false);}
const choose=(n,pat,cb)=>{let used=new Set(),s=[];function go(i){if(i===pat.length){cb(s);return;}for(let j=0;j<n;j++)if(!used.has(j)&&(!i||pat[i]!==pat[i-1]||j>s[i-1])){used.add(j);s.push(j);go(i+1);s.pop();used.delete(j);}}go(0);};
function shift(a,h){const c=Array(a.length).fill(0);for(let t=a.length-1;t>=0;t--){for(let j=a.length-1;j>0;j--)c[j]=mod(c[j-1]-h*c[j]);c[0]=mod(a[t]-h*c[0]);}return c;}


const B=Array.from({length:13},()=>[]);for(let a=1;a<17;a++)for(let b of R)for(let c of R)for(let d of R)for(let e of R)for(let f of R){let C=[f,e,d,c,b,0,a],n=0,q=0;for(let t of R){let u=C.reduceRight((s,x)=>(s*t+x)%17,0); n+=u;if(n>51)break;q+=u*u;}if(n===51){let w=(q-153)/34;if(w<=12)B[w].push(C);}}
if(B[0].length||B[1].length||B.reduce((s,a)=>s+a.length,0)!==448||B.findLastIndex(x=>x.length)!==8)throw Error("sextic extrema");
const bank=R.map(()=>[]);for(let w=2;w<=12;w++)for(let C of B[w])bank[C[6]].push([w,C]);
const masks=reps(8);let hit=0,hist={},tries=Array(5).fill(0),first=null,grid=0,gridHist={};
function add(w,C){let s=w.slice().sort((a,b)=>a-b).join(',');hist[s]=(hist[s]??0)+1;}
for(let mask of masks){const D=mask.map(i=>F[i]),models=new Map();
 function M(j,ord){let k=j+':'+ord.join(',');if(!models.has(k))models.set(k,model(ord.map(i=>D[i]),j));return models.get(k);}
 solve(model(D,6),Array(7).fill(0),raw=>{
 for(let scale of [1,3]){
 const a=raw.map(q=>mod(q*scale)),seq=a.map(q=>bank[q]);
 function rec(j,seq){
 if(j===-1){if(seq.some(l=>l.length!==1))throw Error('profile collision');const w=seq.map(l=>l[0][0]);if(w.reduce((s,a)=>s+a,0)!==21)return;let profiles=seq.map(l=>l[0][1]);hit++;add(w,profiles);first??={mask,w,profiles};
  for(let x of R)for(let y of R){let z=-21;for(let i=0;i<D.length;i++){const [A,B]=D[i],t=mod(A*x+B*y);z+=profiles[i].reduceRight((S,v)=>(S*t+v)%p,0);}
  if(z!==0&&z!==17)return;
  }grid++;const p=w.slice().sort((a,b)=>a-b).join(',');gridHist[p]=(gridHist[p]||0)+1;return;
 }
 const cand=seq.map(l=>{let g=R.map(()=>[]);for(let b of l)g[b[1][j]].push(b);return g;});
 const vv=cand.map(g=>g.map((l,t)=>[t,l[0]?.[0]??50]).filter(z=>z[1]<50));
 const low=vv.map(l=>Math.min(...l.map(v=>v[1]))),base=low.reduce((s,a)=>s+a,0);if(base>21)return;
 const ord=R.slice(0,8).sort((i,k)=>vv[k].length-vv[i].length||i-k),m=M(j,ord),r=j+1;
 let slot=[],cost=base;
 const cons=m.A.map(row=>mod((j===0?21:0)*row[8]));
 function dfs(t,cost){
  if(t<8){for(let [v,w] of vv[ord[t]])if(cost+w-low[ord[t]]<=21){slot[t]=v;dfs(t+1,cost+w-low[ord[t]]);}return;}
  for(let i=0;i<r;i++){let v=cons[i];for(let k=r;k<8;k++)v-=m.A[i][k]*slot[k];slot[i]=mod(v);let list=cand[ord[i]][slot[i]];if(!list.length)return;cost+=list[0][0]-low[ord[i]];if(cost>21)return;}
  let next=seq.slice();for(let i=0;i<8;i++)next[ord[i]]=cand[ord[i]][slot[i]];
  tries[j]++;rec(j-1,next);
 }dfs(r,base);
 }
 rec(4,seq);
 }
 },true);
}
if(hit||grid||String(tries)!=="0,1,1,1,1"||masks.length!==17)throw Error("tight sextic census");console.log({orbits:masks.length,hit,grid,tries});
