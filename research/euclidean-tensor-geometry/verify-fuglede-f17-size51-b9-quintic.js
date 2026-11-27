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
const CAT={};for(let a=1;a<17;a++)for(let b of R)for(let c of R)for(let d of R)for(let e of R){let A=[e,d,c,b,0,a],n=0;for(let t of R){let u=A.reduceRight((s,z)=>(s*t+z)%17,0);if(u>9){n=1000;break;}n+=u;}if(n===51){if(CAT[a])throw Error("quintic leading");CAT[a]=A;}}if(Object.keys(CAT).length!==16)throw Error("quintic count");

const prof=R.map(a=>a&&R.map(h=>shift(CAT[a],h))),n=9,masks=reps(9);let tests=0, hits=0,physical=0,ex=null;
for(let S of masks){const D=S.map(i=>F[i]),V=Array.from({length:4},(_,k)=>model(D,k).V),M5=model(D,5),M4=model(D.slice(2),4);
 solve(M5,Array(6).fill(0),A=>{if(A.some(a=>!a))return;
 solve(M4,Array(5).fill(0),B=>{B=[0,0,...B];tests++;let C=A.map((a,j)=>prof[a][mod(-B[j]*iv[mod(5*a)])]);
 for(let k=0;k<=3;k++)for(let row of V[k])if(mod(row.reduce((s,x,i)=>s+x*C[i][k],k===0?-24:0)))return;
 hits++;
 for(let x of R)for(let y of R){let q=-24;for(let i=0;i<n;i++){let [a,b]=D[i],t=mod(a*x+b*y);q+=C[i].reduceRight((s,v)=>(s*t+v)%p,0);}if(q<0||q>51||q%17)return;}
 physical++;ex??={S,A:A.slice(),B,C};
 });},true);
}
if(masks.length!==17||tests!==889253||hits||physical)throw Error("b9 quintic");console.log({masks:masks.length,tests,hits,physical});
