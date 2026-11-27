function generate34(d,cap){
const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1)), POW=R.map(t=>R.slice(0,d+1).map(j=>m(t**j)));
const A=R.slice(0,d+1),B=A.map(i=>{
 let g=[1],den=1;
 for(let j of A)if(i!==j){let w=Array(g.length+1).fill(0);for(let k=0;k<g.length;k++){w[k]=m(w[k]-j*g[k]);w[k+1]=m(w[k+1]+g[k]);}g=w;den=m(den*(i-j));}
 return g.map(z=>m(z*iv[den]));
});
const b=d-1,c=d,det=iv[m(B[b][d-1]*B[c][d]-B[c][d-1]*B[b][d])];
if(det===undefined)throw Error("two coefficients independent");
const T=R.map(x=>B.map(Q=>m(Q.reduce((s,a,j)=>s+a*POW[x][j],0))));
const I=R.slice(1),v=Array(d+1).fill(0),seen=new Set(),all=[],report=[];
for(let a of I){if(seen.has(a))continue;
 const o=new Map();for(let u of I){const k=m(a*POW[u][d]);if(!o.has(k))o.set(k,u);seen.add(k);}
 let n=0,Qlo=Infinity,Qhi=0;
 function go(k,S,Q,L,H){
  if(k<b){for(let u=0;u<=cap&&S+u<=34;u++){v[k]=u;go(k+1,S+u,Q+u*u,L+u*B[k][d-1],H+u*B[k][d]);}return;}
  const r=m(-L),s=m(a-H),u=m((r*B[c][d]-s*B[c][d-1])*det),w=m((s*B[b][d-1]-r*B[b][d])*det);
  if(u>cap||w>cap)return;v[b]=u;v[c]=w;S+=u+w;Q+=u*u+w*w;if(S>34||S+(16-d)*cap<34)return;
  for(let x=d+1;x<17;x++){const row=T[x];let y=0;for(let j=0;j<=d;j++)y+=row[j]*v[j];y%=17;
   if(y>cap||S+y>34||S+y+(16-x)*cap<34)return;S+=y;Q+=y*y;
  }if(S!==34)return;
  const f=R.slice(0,d+1).map(j=>m(B.reduce((z,row,i)=>z+row[j]*v[i],0))),q=(Q-68)/2;
  if(f[d]!==a||f[d-1]!==0||!Number.isInteger(q)||q<=0)throw Error("mass34");
  n++;Qlo=Math.min(Qlo,q);Qhi=Math.max(Qhi,q);
  for(let u of o.values())all.push([q,f.map((x,j)=>m(x*POW[u][j]))]);
 }
 go(0,0,0,0,0);report.push({a,n,orbit:o.size,Qlo,Qhi});
}
return {all,report};
}

const B6=generate34(6,6).all;if(B6.length!==16)throw Error("cap-six profile count");
const B7=generate34(7,6).all;if(B7.length!==48)throw Error("cap-six profile count");
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
const lower=R.map(()=>[]),high=R.map(()=>[]);
for(const [w,a] of B6)lower[a[6]].push([w,a]);for(const [w,a] of B7)high[a[7]].push([w,a]);
const qs=R.map(a=>a&&R.map(h=>lower[a].map(([w,c])=>[w,shift(c,h).concat(0)]))),ss=R.map(a=>R.map(h=>high[a].map(([w,c])=>[w,shift(c,h)])));
const masks=reps(11);let hit=0,hitT=0,grid=0,gridT=0,examples=[],tries=Array(6).fill(0);
for(let mask of masks){const D=mask.map(i=>F[i]),models=new Map();let tests=0;
 function M(j,ord){let k=j+':'+ord.join(',');if(!models.has(k))models.set(k,model(ord.map(i=>D[i]),j));return models.get(k);}
 const all=R.slice(0,11);solve(M(7,all),Array(8).fill(0),raw=>{
 for(let scale of [1]){
 const a=raw.map(q=>mod(q*scale)),ou=a.map((x,i)=>x===0?i:-1).filter(i=>i>=0);if(ou.length>2)continue;
 const rem=all.filter(i=>a[i]).slice(0,2),piv=all.filter(i=>!rem.includes(i));
 solve(M(6,piv),Array(7).fill(0),c5=>{
  let b=Array(11).fill(0);piv.forEach((i,k)=>b[i]=c5[k]);if(ou.some(i=>!b[i]))return;
  let seq=a.map((x,i)=>x?ss[x][mod(-b[i]*iv[mod(7*x)])]:qs[b[i]].flat());tests++;rec(5,seq);
 }); 
 }
 },true);
 function rec(j,seq){
 if(j===-1){if(seq.some(l=>l.length!==1))throw Error('profile collision');const w=seq.map(l=>l[0][0]);let wt=w.reduce((s,a)=>s+a,0);if(wt!==255)return;
  let profiles=seq.map(l=>l[0][1]);hit++;if(wt===255)hitT++;
  for(let x of R)for(let y of R){let z=-20;for(let i=0;i<D.length;i++){const [A,B]=D[i],t=mod(A*x+B*y);z+=profiles[i].reduceRight((S,v)=>(S*t+v)%p,0);}if(z!==0&&z!==17)return;}
  grid++;if(wt===255)gridT++;if(examples.length<3)examples.push({mask,w,profiles});return;
 }
 const cand=seq.map(l=>{let g=R.map(()=>[]);for(let b of l)g[b[1][j]].push(b);return g;});
 const vv=cand.map(g=>g.map((l,t)=>[t,l.length?0:Infinity]).filter(z=>Number.isFinite(z[1])));if(vv.some(x=>!x.length)||seq.reduce((s,l)=>s+Math.min(...l.map(v=>v[0])),0)>255)return;
 const ord=all.slice().sort((i,k)=>vv[k].length-vv[i].length||i-k),m=M(j,ord),r=j+1;
 let slot=[];
 const cons=m.A.map(row=>mod((j===0?20:0)*row[11]));
 function dfs(t){
  if(t<11){for(let [v,w] of vv[ord[t]]){slot[t]=v;dfs(t+1);}return;}
  for(let i=0;i<r;i++){let v=cons[i];for(let k=r;k<11;k++)v-=m.A[i][k]*slot[k];slot[i]=mod(v);if(!cand[ord[i]][slot[i]].length)return;}
  let next=seq.slice();for(let i=0;i<11;i++)next[ord[i]]=cand[ord[i]][slot[i]];
  tries[j]++;rec(j-1,next);
 }dfs(r);
 }
 if(tests!==85412)throw Error("b11 septic centers");
}
if(masks.length!==10||hit||grid||String(tries)!=="0,0,0,0,0,48537")throw Error("b11 septic");console.log({masks:masks.length,hit,grid,tries});