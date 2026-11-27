'use strict';

const p=17,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,iv=R.map(a=>R.find(b=>m(a*b)===1));
function solve(A,B){let M=A.map((x,i)=>[...x,m(B[i])]),n=A.length;for(let j=0;j<n;j++){let k=M.findIndex((x,i)=>i>=j&&x[j]);if(k<0)throw Error("rank");[M[j],M[k]]=[M[k],M[j]];M[j]=M[j].map(x=>m(x*iv[M[j][j]]));for(let i=0;i<n;i++)if(i!==j){let f=M[i][j];M[i]=M[i].map((x,k)=>m(x-f*M[j][k]));}}return M.map(x=>x[n]);}
const L=R.map(()=>[]),G=R.map(()=>new Set());let total4=0,total16=0;
for(let a=1;a<p;a++)for(let b of R)for(let c of R)for(let d of R){
 let V=R.map(x=>m(a*x**4+b*x*x+c*x+d)),s=V.reduce((a,b)=>a+b),k=(136-s)/p;
 if(k<0||k%1||k>V.filter(x=>!x).length)continue;
 let w=(V.reduce((s,n)=>s+n*(n-1)/2,0)+136*k-17*8*7/2)/p;
 if(w===4){L[a].push([b,c,d]);total4++;}
 if(w===16){G[a].add([b,c,d].join());total16++;}
}
let masks=0,leads=0,branches=0,tuples=0,cong=0,ex=null;
for(let s=2;s<p;s++)for(let t=s+1;t<p;t++)for(let u=t+1;u<p;u++){
 masks++;
 const F=[[1,0],[0,1],[1,1],[1,s],[1,t],[1,u]],powers=d=>R.slice(0,d+1).map(j=>F.map(([x,y])=>m(x**(d-j)*y**j)));
 const A=powers(4),B=powers(2);
 const a0=solve(A.map(r=>r.slice(0,5)),A.map(r=>-r[5]));
 for(let a5=1;a5<p;a5++){
  let a=[...a0.map(x=>m(x*a5)),a5];if(a.some(x=>!x))continue;leads++;
  for(let j=0;j<6;j++){
   if(!G[a[j]].size||a.some((x,i)=>i!==j&&!L[x].length))continue;branches++;
   let C=[];
   function go(i,b0,b1,b2,c0,c1,d0){
    if(i===6){
     tuples++;
     const [x,y]=F[j],b=m(x?-b0:-b2),c=m(x?-c0:-c1),d=m(40-d0);
     if(m(b0+b*x*x)||m(b1+b*x*y)||m(b2+b*y*y)||m(c0+c*x)||m(c1+c*y)||!G[a[j]].has([b,c,d].join()))return;
     cong++;ex??={F,a,C:C.slice(),j,high:[b,c,d]};
     return;
    }
    if(i===j){go(i+1,b0,b1,b2,c0,c1,d0);return;}
    const [x,y]=F[i];
    for(const E of L[a[i]]){const [b,c,d]=E;C.push(E);go(i+1,b0+b*x*x,b1+b*x*y,b2+b*y*y,c0+c*x,c1+c*y,d0+d);C.pop();}
   }
   go(0,0,0,0,0,0,0);
  }
 }
}
if(total4!==28||total16!==2640||masks!==455||leads!==7280||branches!==10200||tuples!==741720||cong)throw Error("quartic pattern census");
console.log({total4,total16,masks,leads,branches,tuples,cong});

const q=new Set();
for(let a=1;a<p;a++)for(let c of R){
 const f=R.map(x=>m(a*x*x+c)),l=(136-f.reduce((s,n)=>s+n,0))/p;
 if(l<0||l%1||l>f.filter(x=>!x).length)continue;
 const w=(f.reduce((s,n)=>s+n*(n-1)/2,0)+136*l-476)/p;
 q.add([w,c].join());
}
const xy=[...q].map(x=>x.split(",").map(Number));let ns=0,S=0;
for(let a=0;a<xy.length;a++)for(let b=a;b<xy.length;b++)for(let c=b;c<xy.length;c++)for(let d=c;d<xy.length;d++){
 const A=[xy[a],xy[b],xy[c],xy[d]];
 if(A.reduce((s,t)=>s+t[0],0)!==36||m(A.reduce((s,t)=>s+t[1],0))!==7)continue;
 ns++;S=Math.max(S,A.reduce((s,t)=>s+t[0]**2,0));
}
if(xy.length!==18||ns!==4||S!==330)throw Error("quadratic pattern census");
const boundLines={};
for(let d=12;d<=14;d++){
 let upper=18;
 for(let k=2;k<=d;k++)for(let t=2;t<=Math.min(k,d-5);t++)
  upper=Math.max(upper,Math.min(18*k-Math.ceil(k*(k-1)/t),17*k+1-(k-t)*(t-1)));
 if(upper>17*(d-1)+2)throw Error("line union bound");
 boundLines[d]=upper;
}
const W=1124,C=36,P=307,Q=12252;
const u=18*W*W-C*W*P,v=Q*P-W*W;
if(u<=0||v<0||BigInt(u)**2n<=17n*BigInt(v)**2n)throw Error("weight mixing");
console.log({quadraticTuples:ns,maxSquare:S,boundLines,u,v});
