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




const B=Array.from({length:13},()=>[]);for(let a=1;a<17;a++)for(let b of R)for(let c of R)for(let d of R)for(let e of R)for(let f of R){let C=[f,e,d,c,b,0,a],n=0,q=0;for(let t of R){let u=C.reduceRight((s,x)=>(s*t+x)%17,0); if(u>9){n=1000;break;}n+=u;if(n>51)break;q+=u*u;}if(n===51){let w=(q-153)/34;if(w<=12)B[w].push(C);}}

const Q=[null], sextic=R.map(()=>[]);for(let a=1;a<17;a++)for(let b of R)for(let c of R)for(let d of R)for(let e of R){let A=[e,d,c,b,0,a],n=0;for(let t of R){let u=A.reduceRight((s,z)=>(s*t+z)%17,0);if(u>9){n=1000;break;}n+=u;}if(n===51){if(Q[a])throw Error("quintic leading");Q[a]=A;}}
if(Q.filter(Boolean).length!==16||B.reduce((s,a)=>s+a.length,0)!==120)throw Error("profile catalogue");
for(let w=2;w<=12;w++)for(let A of B[w])sextic[A[6]].push([w,A]);
function shift(a,h){const c=Array(a.length).fill(0);for(let t=a.length-1;t>=0;t--){for(let j=a.length-1;j>0;j--)c[j]=mod(c[j-1]-h*c[j]);c[0]=mod(a[t]-h*c[0]);}return c;}
const qs=R.map(a=>a&&R.map(h=>shift(Q[a],h).concat(0))), ss=R.map(a=>R.map(h=>sextic[a].map(([w,c])=>[w,shift(c,h)])));
const masks=reps(9);let hit=0,hitT=0,grid=0,gridT=0,examples=[],tries=Array(5).fill(0);
for(let mask of masks){const D=mask.map(i=>F[i]),models=new Map();let tests=0;
 function M(j,ord){let k=j+':'+ord.join(',');if(!models.has(k))models.set(k,model(ord.map(i=>D[i]),j));return models.get(k);}
 const all=R.slice(0,9);solve(M(6,all),Array(7).fill(0),raw=>{
 for(let scale of [1,3]){
 const a=raw.map(q=>mod(q*scale)),ou=a.map((x,i)=>x===0?i:-1).filter(i=>i>=0);if(ou.length>1)continue;
 const rem=all.filter(i=>a[i]).slice(0,2),piv=all.filter(i=>!rem.includes(i));
 solve(M(5,piv),Array(6).fill(0),c5=>{
  let b=Array(9).fill(0);piv.forEach((i,k)=>b[i]=c5[k]);if(ou.length&&!b[ou[0]])return;
  let seq=a.map((x,i)=>x?ss[x][mod(-b[i]*iv[mod(6*x)])]:qs[b[i]].map(c=>[4,c]));tests++;rec(4,seq);
 }); 
 }
 },true);
 function rec(j,seq){
 if(j===-1){if(seq.some(l=>l.length!==1))throw Error('profile collision');const w=seq.map(l=>l[0][0]);let wt=w.reduce((s,a)=>s+a,0);
  let profiles=seq.map(l=>l[0][1]);hit++;if(wt===21)hitT++;
  for(let x of R)for(let y of R){let z=-24;for(let i=0;i<D.length;i++){const [A,B]=D[i],t=mod(A*x+B*y);z+=profiles[i].reduceRight((S,v)=>(S*t+v)%p,0);}if(z<0||z>51||z%17)return;}
  grid++;if(wt===21)gridT++;if(examples.length<3)examples.push({mask,w,profiles});return;
 }
 const cand=seq.map(l=>{let g=R.map(()=>[]);for(let b of l)g[b[1][j]].push(b);return g;});
 const vv=cand.map(g=>g.map((l,t)=>[t,l[0]?.[0]??50]).filter(z=>z[1]<50));if(vv.some(x=>!x.length))return;
 const ord=all.slice().sort((i,k)=>vv[k].length-vv[i].length||i-k),m=M(j,ord),r=j+1;
 let slot=[];
 const cons=m.A.map(row=>mod((j===0?24:0)*row[9]));
 function dfs(t){
  if(t<9){for(let [v,w] of vv[ord[t]]){slot[t]=v;dfs(t+1);}return;}
  for(let i=0;i<r;i++){let v=cons[i];for(let k=r;k<9;k++)v-=m.A[i][k]*slot[k];slot[i]=mod(v);if(!cand[ord[i]][slot[i]].length)return;}
  let next=seq.slice();for(let i=0;i<9;i++)next[ord[i]]=cand[ord[i]][slot[i]];
  tries[j]++;rec(j-1,next);
 }dfs(r);
 }
 if(tests!==594)throw Error("center assignments");
}
if(masks.length!==17||hit||hitT||grid||gridT||String(tries)!=="0,0,0,7,4846")throw Error("b9 sextic");console.log({hit,hitT,grid,gridT,tries});
