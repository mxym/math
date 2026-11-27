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

const bank=R.map(()=>[]), weights=[];
function weight(C){
  let q=0,n=0;
  for(let t of R){const x=C.reduceRight((s,a)=>(s*t+a)%p,0);n+=x;q+=x*x;}
  return n===68?(q-272)/34:-1;
}
for(let a=1;a<p;a++) for(let u of R) for(let v of R) for(let c of R){
  const C=[c,v,u,0,a], w=weight(C);
  if(w>=0){bank[a].push(C);weights.push(w);}
}
if(!weights.every(Number.isInteger)||Math.min(...weights)!==4||Math.max(...weights)!==11)throw Error('quartic weights');
let hits=0,tests=0,physical=0;
const masks=reps(6);
for(const mask of masks){
  const D=mask.map(x=>F[x]), V=Array.from({length:3},(_,k)=>model(D,k).V);
  solve(model(D,4),Array(5).fill(0),AA=>{
    for(const scalar of [1,3,9,10]){
      const A=AA.map(x=>mod(x*scalar)), C=[null];
      function rec(i){
        if(i<6){for(const g of bank[A[i]]){C[i]=g;rec(i+1);}return;}
        tests++;
        const u=[0,0,0,0,A[0]];
        for(let k=0;k<=2;k++){
          const v=V[k], y=v.map(row=>mod((k===0?20:0)-row.reduce((s,a,j)=>s+(C[j]?.[k]??0)*a,0)));
          const pin=v.findIndex(row=>row[0]);
          u[k]=mod(y[pin]*iv[v[pin][0]]);
          if(v.some((row,j)=>mod(row[0]*u[k]-y[j])))return;
        }
        if(weight(u)<0)return;
        hits++;
        const T=C.slice();T[0]=u;
        for(let x of R)for(let y of R){
          let z=-20;
          for(let j=0;j<6;j++){const t=mod(D[j][0]*x+D[j][1]*y);z+=T[j].reduceRight((a,c)=>(a*t+c)%p,0);}
          if(z<0||z>68||z%p)return;
        }
        physical++;
      }
      rec(1);
    }
  },true);
}
if(masks.length!==10||tests!==55398||hits!==12||physical!==0)throw Error('quartic pencils');
console.log({orbits:masks.length,quarticProfiles:weights.length,weightRange:[4,11],tests,hits,physical});
