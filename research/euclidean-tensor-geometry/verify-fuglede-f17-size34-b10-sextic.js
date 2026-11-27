const BANK={};{function save(d,b){BANK[d]=b;}
const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
for(const cap of [8])for(let d=6;d<=6;d++){
 const A=R.slice(0,d+1),B=A.map(i=>{
  let g=[1],den=1;
  for(const j of A)if(j!==i){
   const w=Array(g.length+1).fill(0);for(let k=0;k<g.length;k++){w[k]=m(w[k]-j*g[k]);w[k+1]=m(w[k+1]+g[k]);}g=w;den=m(den*(i-j));
  }
  return g.map(v=>m(v*iv[den]));
 });
 const j=A.findLast(b=>B[b][d-1]!==0);
 const P=R.map(x=>B.map(g=>m(g.reduce((s,a,i)=>s+a*x**i,0))));
 const v=new Uint8Array(17),free=A.filter(t=>t!==j);let count=0,max=0,ex;const bank=[];
 
 function go(i,S,Q,L,V){
  if(i<free.length){
   const x=free[i],b=B[x][d-1],l=B[x][d];
   for(let a=0;a<=cap;a++){v[x]=a;go(i+1,S+a,Q+a*a,L+a*b,V+a*l);}return;
  }
  const a=m(-L*iv[B[j][d-1]]);if(a>cap||!m(V+a*B[j][d]))return;
  v[j]=a;S+=a;Q+=a*a;
  for(let x=d+1;x<p;x++){
   const row=P[x];let n=0;for(let k=0;k<=d;k++)n+=row[k]*v[k];n%=p;
   if(n>cap||S+n>34||(S+n)+(16-x)*cap<34)return;
   S+=n;Q+=n*n;v[x]=n;
  }
  if(S!==34)return;count++;const cc=B[0].map((_,k)=>m(B.reduce((s,b,i)=>s+b[k]*v[i],0)));bank.push([(Q-68)/2,cc]);
  if(Q>max){max=Q;ex=Array.from(v);}
 }
 go(0,0,0,0,0);if(count!==(d===6?16:d===7?64:568))throw Error("profile count");save(d,bank);
}
}
const B=BANK[6];
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

const CAT={};for(let [w,a] of B)CAT[a[6]]=a;
const prof=R.map(a=>a&&R.map(h=>shift(CAT[a],h))),n=10,masks=reps(10);let tests=0, hits=0,physical=0,ex=null;
for(let S of masks){const D=S.map(i=>F[i]),V=Array.from({length:5},(_,k)=>model(D,k).V),M6=model(D,6),M5=model(D.slice(2),5),tmp=[];
 solve(M6,Array(7).fill(0),Z=>{if(Z.some(a=>!a))return;
 for(let scale of [1,3]){
 const A=Z.map(x=>mod(x*scale)); const Bf=A.map(a=>prof[a]),Biv=A.map(a=>iv[mod(-6*a)]);
 solve(M5,Array(6).fill(0),B=>{tests++;
 let C=A.map((a,j)=>j<2?Bf[j][0]:Bf[j][mod(B[j-2]*Biv[j])]);
 for(let k=4;k>=0;k--)for(let row of V[k]){let s=k===0?-18:0;for(let i=0;i<10;i++)s+=row[i]*C[i][k];if(mod(s))return;}
 hits++;
 for(let x of R)for(let y of R){let q=-18;for(let i=0;i<n;i++){let [a,b]=D[i],t=mod(a*x+b*y);q+=C[i].reduceRight((s,v)=>(s*t+v)%p,0);}if(q<0||q>34||q%17)return;}
 physical++;ex??={S,A:A.slice(),B:B.slice(),C};
 });}},true);
}
if(masks.length!==17||tests!==1690072||hits||physical)throw Error("b10 sextic");console.log({masks:masks.length,tests,hits,physical});
