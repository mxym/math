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

const bank={};for(let a=1;a<p;a++)for(let b of R)for(let c of R)for(let d of R)for(let e of R){const A=[e,d,c,b,0,a],w=weight(A);if(w>=0)(bank['5:'+w+':'+a]??=[]).push(A);}
function weight(C){let q=0,n=0;for(let t of R){let x=C.reduceRight((s,a)=>(s*t+a)%p,0);n+=x;q+=x*x;}return n===68?(q-272)/34:-1;}const zero=d=>Array(d+1).fill(0);
const patterns=[[8],[7,4],[6,5],[6,4,4],[5,5,4],[5,4,4,4],[4,4,4,4,4]];
for(let pi=0;pi<patterns.length;pi++){
 const pat=patterns[pi],n=7, masks=reps(n),expected=pat.concat(Array(n-pat.length).fill(3));let tests=0,hits=0,first=null,steps=Array(5).fill(0);
 for(let mask of masks){const D=mask.map(i=>F[i]),M6=model(D,5), models=new Map();
  function matrices(order,k){let z=k+':'+order.join(',');if(!models.has(z))models.set(z,model(order.map(i=>D[i]),k));return models.get(z);}
 solve(M6,zero(5),vec=>{
 for(let scale of [1]){let a=vec.map(x=>mod(x*scale)),z=a.indexOf(0),g=a.filter(x=>!x).length;
 if(g>0)continue;
 const piv=[];for(let j=0;j<n&&piv.length<2;j++)if(a[j])piv.push(j);
 const other=R.slice(0,n).filter(j=>!piv.includes(j)),M5=matrices(other,4);
 solve(M5,zero(4),bb=>{let b=Array(n).fill(0);for(let i=0;i<other.length;i++)b[other[i]]=bb[i];
 const banks=a.map((x,i)=>{if(!x)return [];const h=mod(-b[i]*iv[mod(5*x)]);return Array.from({length:13},(_,w)=>(bank['5:'+w+':'+x]??[]).map(v=>shift(v,h)));});
 choose(n,pat,H=>{
 if(g&&H[0]!==z)return;
 const h=H[0],weights=Array(n).fill(3);H.forEach((j,i)=>weights[j]=pat[i]);
 const list=weights.map((w,i)=>i===h?null:banks[i][w]),fixed=[0,0,0,0,b[h],a[h]];
 if(list.some(v=>v&&v.length===0))return;
 tests++;
 function rec(k, ls){
 if(k<0){if(weight(fixed)!==pat[0])return;hits++;first??={mask,a:a.slice(),b,H:H.slice(),fixed:fixed.slice(),known:ls.map(x=>x?.[0]??null)};return;}
 const vals=ls.map(s=>s&&[...new Set(s.map(x=>x[k]))]);
 const order=[h,...R.slice(0,n).filter(i=>i!==h).sort((i,j)=>vals[j].length-vals[i].length||i-j)];
 const M=matrices(order,k),r=M.r;
 const Y=k===0?mod(4*(n-1)):0, bv=M.A.slice(0,r).map(row=>mod(row[n]*Y)), tail=[];
 function free(t){
 if(t<n){for(let x of vals[order[t]]){tail[t]=x;free(t+1);}return;}
 let result=ls.slice();
 for(let j=0;j<r;j++){let x=bv[j];for(let t=r;t<n;t++)x-=M.A[j][t]*tail[t];tail[j]=mod(x);if(j&& !vals[order[j]].includes(tail[j]))return;}
 for(let j=1;j<n;j++){let i=order[j],x=tail[j];if(vals[i].length>1)result[i]=ls[i].filter(q=>q[k]===x);}
 steps[k]++;
 fixed[k]=tail[0];rec(k-1,result);
 }free(r);
 }rec(3,list);
 });
 });}
 },true);}
 if(masks.length!==10||tests!==[70,420,420,1050,1050,1400,210][pi]||hits)throw Error("quintic tight census");console.log({pi,expected,orbits:masks.length,tests,steps,hits});}
