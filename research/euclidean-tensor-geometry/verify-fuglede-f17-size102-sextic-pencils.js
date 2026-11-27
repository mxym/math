'use strict';
function centeredWeightTwo(){

const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
const L=[],C=[];
for(let i=0;i<7;i++){
 let a=[1],d=1;for(let j=0;j<7;j++)if(i!==j){
  const g=Array(a.length+1).fill(0);for(let k=0;k<a.length;k++){g[k]=m(g[k]-j*a[k]);g[k+1]=m(g[k+1]+a[k]);}
  a=g;d=m(d*(i-j));
 }C.push(a.map(x=>m(x*iv[d])));
}
for(let x=0;x<p;x++)L.push(C.map(a=>m(a.reduce((s,k,i)=>s+k*x**i,0))));
let A=new Int8Array(7),n=0,all=0,K=R.map(()=>[]);
function go(i,q,s){
 if(i<7){for(let t=-6;t<=8;t++){if(q+t*t<=68){A[i]=t;go(i+1,q+t*t,s+t);}}return;}
 n++;
 for(let x=7;x<17;x++){
  const a=L[x];let t=m(A[0]*a[0]+A[1]*a[1]+A[2]*a[2]+A[3]*a[3]+A[4]*a[4]+A[5]*a[5]+A[6]*a[6]);if(t>8)t-=17;
  if(t<-6)return;q+=t*t;if(q>68)return;s+=t;
 }
 if(q!==68||s!==0)return;
 const cs=C[0].map((_,k)=>m(A.reduce((s,t,j)=>s+t*C[j][k],k===0?6:0)));
 if(cs[6]&&cs[5]===0){all++;K[cs[6]].push(cs);}
}
go(0,0,0);if(n!==12362679||all!==56)throw Error("weight2 census");
console.log({n,all});return K;

}
const weight2=centeredWeightTwo();
'use strict';
const p=17,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*18+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):17;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const masks={};
function choose(S,k){if(S.length===8){let [j,t]=canonical(S);masks[j]=t;return;}for(let x=k;x<=17-(8-S.length);x++)choose([...S,x],x+1);}choose([0,1,17],2); // initial slope ordering is immaterial
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}

const W=[2,2,2,2,2,2,2,21]; 
const getWeight=A=>{
 let v=r.map(t=>m(A.reduceRight((s,a)=>s*t+a,0))),sum=v.reduce((s,n)=>s+n),z=v.filter(x=>!x).length,k=(102-sum)/17;
 if(k<0||k>z||k%1)return -1;
 return (v.reduce((s,n)=>s+n*(n-1)/2,0)+136*k-255)/17;
};
let all={};
for(const S of Object.values(masks)){
 const F=S.map(s=>V[s]),pow=d=>r.slice(0,d+1).map(j=>F.map(([a,b])=>m(a**(d-j)*b**j)));
 const D=r.slice(0,5).map(d=>pow(d)), lead=solveCols(F,6,8);
 const H={shapes:[{positions:0,tuples:0,linear:0,match:0},{positions:0,tuples:0,linear:0,match:0}],ex:null};
 for(const a7 of [1,3]){
  const A=lead([a7]);
  for(let shape=0;shape<2;shape++)for(let h=0;h<8;h++)for(let j=shape?0:8;j<(shape?8:9);j++){
   if(j===h)continue;
   if(A.some((a,k)=>k!==h&&k!==j&&!weight2[a].length))continue;
   const bins=r.slice(0,5).map(d=>new Int32Array(d+1)),X=H.shapes[shape];X.positions++;
   const coeffH=[0,0,0,0,0,0,A[h]],coeffJ=[0,0,0,0,0,0,A[j]??0],idx=[];
   for(let d=1;d<=4;d++){
    const P=D[d];
    if(shape){
     let f=null;for(let u=0;u<=d&&!f;u++)for(let v=u+1;v<=d;v++){let a=P[u][h],b=P[u][j],c=P[v][h],e=P[v][j],det=m(a*e-b*c);if(det){f=[u,v,m(e*i[det]),m(-b*i[det]),m(-c*i[det]),m(a*i[det])];break;}}
     if(!f)throw Error("direction rank");idx[d]=f;
    }else idx[d]=P.findIndex(row=>row[h]===1);
   }
   function go(k){
    if(k===8){
     X.tuples++;
     for(let d=1;d<=4;d++){
      let P=D[d],Q=bins[d];
      if(shape){
       const [u,v,aa,b,c,e]=idx[d];coeffH[d]=m(-aa*Q[u]-b*Q[v]);coeffJ[d]=m(-c*Q[u]-e*Q[v]);
      }else coeffH[d]=m(-Q[idx[d]]);
      for(let u=0;u<=d;u++)if(m(Q[u]+P[u][h]*coeffH[d]+(shape?P[u][j]*coeffJ[d]:0)))return;
     }
     X.linear++;
     let c=m(42-bins[0][0]);
     if(!shape){coeffH[0]=c;if(getWeight(coeffH)!==19)return;X.match++;H.ex??={A,h,j,coeffH:[...coeffH]};}
     else for(let t=0;t<p;t++){coeffH[0]=t;coeffJ[0]=m(c-t);if(getWeight(coeffJ)!==3||getWeight(coeffH)!==18)continue;X.match++;H.ex??={A,h,j,coeffH:[...coeffH],coeffJ:[...coeffJ]};}
     return;
    }
    if(k===h||k===j){go(k+1);return;}
    for(const a of weight2[A[k]]){
     for(let d=0;d<=4;d++)for(let t=0;t<=d;t++)bins[d][t]+=D[d][t][k]*a[d];
     go(k+1);
     for(let d=0;d<=4;d++)for(let t=0;t<=d;t++)bins[d][t]-=D[d][t][k]*a[d];
    }
   }
   go(0);
  }
 }
 all[S.join()]=H;
}

const cases=Object.values(all),m0=cases.reduce((s,H)=>s+H.shapes[0].match,0),m1=cases.reduce((s,H)=>s+H.shapes[1].match,0);
if(cases.length!==17||m0!==1||m1)throw Error("tight sextic pattern census");
const H=cases.find(H=>H.shapes[0].match),coef=H.ex.coeffH;
const vals=r.map(x=>m(coef.reduceRight((s,a)=>s*x+a,0)));
if(coef.join()!=="0,0,1,0,13,0,4"||vals.reduce((s,n)=>s+n,0)!==102||Math.max(...vals)!==16)throw Error("heavy surviving profile");
console.log({masks:cases.length,matches:[m0,m1],coef,peak:16});

