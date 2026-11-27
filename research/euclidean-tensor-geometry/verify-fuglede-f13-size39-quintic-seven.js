
'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const masks={};
function choose(S,k){if(S.length===7){let [j,t]=canonical(S);masks[j]=t;return;}for(let x=k;x<=13-(7-S.length);x++)choose([...S,x],x+1);}choose([0,1,13],2); // initial slope ordering is immaterial
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}
const catalog=r.map(()=>r.map(()=>[]));const quinticHistogram={};
for(let a=1;a<13;a++)for(let b of r)for(let c of r)for(let d of r)for(let f of r){
 let total=0,q=0,good=true,maximum=0;
 for(let x of r){let y=m((((a*x*x+b)*x+c)*x+d)*x+f);if(y>9){good=false;break;}total+=y;q+=y*(y-1)/2;maximum=Math.max(maximum,y);}
 if(good&&total===39){let w=(q-39)/13;quinticHistogram[w]=(quinticHistogram[w]??0)+1;catalog[a][b].push({c,d,f,w,heavy:maximum>=8});}
}
if(JSON.stringify(quinticHistogram)!==JSON.stringify({1:12,2:108,3:396,4:216,5:120,6:12}))throw Error('quintic profile bounds');
const result={};let ntest=0,feas=0;
for(const S of Object.values(masks)){
 const F=S.map(s=>V[s]), a=solveCols(F,5,7)([1]), B=solveCols(F,3,7);
 const count={},witness={};const hcount={};
 for(let u of r)for(let v of r)for(let z of r){
  const b=B([u,v,z]), L=a.map((aj,j)=>catalog[aj][b[j]]);
  const wt=L.map(l=>l.reduce((s,o)=>Math.min(s,o.w),20)),total=wt.reduce((s,w)=>s+w,0);if(total>15)continue;feas++;
  const L2=L.map((li,j)=>li.map(o=>{const [x,y]=F[j];return {...o,k:[x*x*o.c,2*x*y*o.c,y*y*o.c,o.d*x,o.d*y,o.f].map(m)};}));
  let table=new Map();
  function loop(k,end,w,S,W,minRest,H){
   if(k===end){if(end===3){let key=[w,...S].join();if(!table.has(key))table.set(key,[]);table.get(key).push([W,H]);}
    else{ const target=S.map((x,j)=>m((j===5?18:0)-x));const entries=table.get([15-w,...target].join());
     if(entries)for(let [other,OH] of entries){let key=[...W,...other].sort((a,b)=>a-b).join();count[key]=(count[key]??0)+1;witness[key]??={a,b};const hh=H+OH;if(hh<2)throw Error('heavy profiles missing');const hkey=key+';'+hh;hcount[hkey]=(hcount[hkey]??0)+1;}
    }
    ntest++;return;
   }
   minRest-=wt[k];
   for(let o of L2[k])if(w+o.w+minRest<=15)loop(k+1,end,w+o.w,S.map((x,j)=>m(x+o.k[j])),[...W,o.w],minRest,H+(o.heavy?1:0));
  }
  loop(0,3,0,[0,0,0,0,0,0],[],total,0);
  loop(3,7,0,[0,0,0,0,0,0],[],total,0);
 }
 result[S.join()]={count,witness,hcount};
}
const total={};
for(const {count} of Object.values(result))for(const [key,n] of Object.entries(count))total[key]=(total[key]??0)+n;
if(Object.keys(masks).length!==5||ntest!==129805||feas!==3593||Object.keys(total).length!==3||total["1,1,1,2,3,3,4"]!==2||total["1,1,1,1,3,3,5"]!==1||total["1,1,2,2,3,3,3"]!==9)throw Error("unexpected census");
const peak={};
for(const {hcount} of Object.values(result))for(const [j,k] of Object.entries(hcount)){const w=j.split(';')[1];peak[w]=(peak[w]??0)+k;}
if(JSON.stringify(peak)!==JSON.stringify({2:2,3:10}))throw Error('peak census');
console.log({quinticHistogram,masks:Object.values(masks),ntest,feas,total,peak,result});
