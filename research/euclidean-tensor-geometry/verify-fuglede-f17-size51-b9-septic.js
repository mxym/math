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



const bank=R.map(()=>[]);let mono=[],A=Array(8).fill(0);A[7]=1;
const POW=R.map(t=>R.slice(0,8).map(k=>t**k%17));
function gen(j){if(j<=5){for(let x of R){A[j]=x;gen(j+1);}return;}
 const Y=R.map(t=>mod(A.slice(1).reduce((s,a,k)=>s+a*POW[t][k+1],0)));
 // Occupancy corresponding to t=0 has value c, so only c=0..9.
 for(let c=0;c<=9;c++){let n=0,q=0,good=true;for(let y of Y){let x=(y+c)%17;if(x>9){good=false;break;}n+=x;q+=x*x;}if(good&&n===51)mono.push([c,...A.slice(1)]);}
}gen(1);
for(let l=1;l<17;l++)for(let C of mono){const D=C.map((a,k)=>mod(a*POW[l][k]));let w=R.reduce((s,t)=>{let v=D.reduceRight((z,a)=>(z*t+a)%17,0);return s+v*v;},-153)/34;bank[D[7]].push([w,D]);}
if(mono.length!==107)throw Error('septic catalogue');
const masks=reps(9);let hit=0,hist={},tries=Array(6).fill(0),first=null,grid=0,gridHist={};
function add(w,C){let s=w.slice().sort((a,b)=>a-b).join(',');hist[s]=(hist[s]??0)+1;}
for(let mask of masks){const D=mask.map(i=>F[i]),models=new Map();
 function M(j,ord){let k=j+':'+ord.join(',');if(!models.has(k))models.set(k,model(ord.map(i=>D[i]),j));return models.get(k);}
 solve(model(D,7),Array(8).fill(0),raw=>{
 for(let scale of [1]){
 const a=raw.map(q=>mod(q*scale)),seq=a.map(q=>bank[q]);
 function rec(j,seq){
 if(j===-1){if(seq.some(l=>l.length!==1))throw Error('profile collision');const w=seq.map(l=>l[0][0]);let profiles=seq.map(l=>l[0][1]);hit++;add(w,profiles);first??={mask,w,profiles};
  for(let x of R)for(let y of R){let z=-24;for(let i=0;i<D.length;i++){const [A,B]=D[i],t=mod(A*x+B*y);z+=profiles[i].reduceRight((S,v)=>(S*t+v)%p,0);}
  if(z<0||z>51||z%17)return;
  }grid++;const p=w.slice().sort((a,b)=>a-b).join(',');gridHist[p]=(gridHist[p]||0)+1;return;
 }
 const cand=seq.map(l=>{let g=R.map(()=>[]);for(let b of l)g[b[1][j]].push(b);return g;});
 const vv=cand.map(g=>g.map((l,t)=>[t,l[0]?.[0]??50]).filter(z=>z[1]<50));
 const low=vv.map(l=>Math.min(...l.map(v=>v[1]))),base=low.reduce((s,a)=>s+a,0);if(base>100)return;
 const ord=R.slice(0,9).sort((i,k)=>vv[k].length-vv[i].length||i-k),m=M(j,ord),r=j+1;
 let slot=[],cost=base;
 const cons=m.A.map(row=>mod((j===0?24:0)*row[9]));
 function dfs(t,cost){
  if(t<9){for(let [v,w] of vv[ord[t]])if(cost+w-low[ord[t]]<=100){slot[t]=v;dfs(t+1,cost+w-low[ord[t]]);}return;}
  for(let i=0;i<r;i++){let v=cons[i];for(let k=r;k<9;k++)v-=m.A[i][k]*slot[k];slot[i]=mod(v);let list=cand[ord[i]][slot[i]];if(!list.length)return;cost+=list[0][0]-low[ord[i]];if(cost>100)return;}
  let next=seq.slice();for(let i=0;i<9;i++)next[ord[i]]=cand[ord[i]][slot[i]];
  tries[j]++;rec(j-1,next);
 }dfs(r,base);
 }
 rec(5,seq);
 }
 },true);
}
if(masks.length!==17||hit||grid||String(tries)!=="0,7,7,80,162103,83521")throw Error("b9 septic");console.log({hit,grid,tries});
