'use strict';
// Necessary centered quartic profiles on a six-direction tight pencil, mass39.
// The affine plane occupation cap is9.

const p=13,m=x=>(x%p+p)%p,r=Array.from({length:p},(_,i)=>i),iv=r.map(a=>r.find(b=>m(a*b)===1)),LST=r.map(()=>[]),tb=r.map(()=>r.map(()=>[])),h={};
function solve(A,B){let M=A.map((x,i)=>[...x,m(B[i])]),n=A.length;for(let c=0;c<n;c++){let j=M.findIndex((x,i)=>i>=c&&x[c]);if(j<0)throw Error('rank');[M[c],M[j]]=[M[j],M[c]];M[c]=M[c].map(x=>m(x*iv[M[c][c]]));for(let i=0;i<n;i++)if(i!==c)M[i]=M[i].map((x,k)=>m(x-M[i][c]*M[c][k]));}return M.map(x=>x[n]);}
for(let a=1;a<p;a++)for(let b of r)for(let c of r)for(let d of r){let v=r.map(t=>m(a*t**4+b*t*t+c*t+d)),z=v.filter(x=>!x).length,k=(39-v.reduce((x,y)=>x+y))/p;if(k%1||k<0||k>z)continue;let w=(v.reduce((s,n)=>s+n*(n-1)/2,0)+78*k-39)/p;h[w]=(h[w]||0)+1;if(w<=5&&k===0&&Math.max(...v)<=9){let e={a,b,c,d,w,k,z};LST[a].push(e);tb[a][b].push(e);}}
let counts={},num=0,examples={};
for(let s=2;s<p;s++)for(let t=s+1;t<p;t++)for(let u=t+1;u<p;u++){
 let L=[[1,0],[0,1],[1,1],[1,s],[1,t],[1,u]],A=r.slice(0,5).map(j=>L.map(([x,y])=>m(x**(4-j)*y**j)));
 let base=solve(A.map(x=>x.slice(0,5)),A.map(x=>-x[5])),B=r.slice(0,3).map(j=>L.map(([x,y])=>m(x**(2-j)*y**j)));
 let I=B.map((x,i)=>solve(B.map(y=>y.slice(3)),[0,1,2].map(j=>+(j===i))));
 for(let a5=1;a5<p;a5++){
  let as=[...base.map(x=>m(x*a5)),a5];if(as.some(x=>!x))continue;num++;
  for(let f0 of LST[as[0]])for(let f1 of LST[as[1]])for(let f2 of LST[as[2]]){
   let w=f0.w+f1.w+f2.w;if(w>9)continue;
   let Bs=B.map(x=>-(x[0]*f0.b+x[1]*f1.b+x[2]*f2.b)),bs=[0,1,2].map(i=>m(Bs.reduce((a,b,j)=>a+b*I[j][i],0)));
   for(let f3 of tb[as[3]][bs[0]])for(let f4 of tb[as[4]][bs[1]]){
    if(w+f3.w+f4.w>13)continue;
    let c5=m(-(f0.c+f2.c+f3.c+f4.c)),d5=m(15-f0.d-f1.d-f2.d-f3.d-f4.d);
    if(m(f1.c+f2.c+s*f3.c+t*f4.c+u*c5))continue;
    for(let f5 of tb[as[5]][bs[2]])if(f5.c===c5&&f5.d===d5&&w+f3.w+f4.w+f5.w===15){
     let fs=[f0,f1,f2,f3,f4,f5],key=fs.map(x=>x.w).sort((a,b)=>a-b).join();counts[key]=(counts[key]||0)+1;examples[key]??={L,fs};
    }
   }
  }
 }
}
if(num!==1980||JSON.stringify(counts)!==JSON.stringify({"2,2,2,2,3,4":720}))throw Error(JSON.stringify({num,counts}));
console.log({h,num,counts});
