function rank(B,p,det=false){
const k=B[0].length, wb=(n,r)=>Array.from({length:1<<n},(_,i)=>i).filter(i=>pop[i]==r),S=wb(k,p), T=wb(k,p+1), where=new Map(T.map((u,i)=>[u,i])), rows=Array.from({length:T.length*16},()=>new Int32Array(S.length*36)), pairs=[];
for(let a=0;a<4;a++)for(let b=a+1;b<4;b++)for(let c=0;c<4;c++)for(let d=c+1;d<4;d++)pairs.push([[a*4+c,b*4+d,1],[b*4+d,a*4+c,1],[a*4+d,b*4+c,det?-1:1],[b*4+c,a*4+d,det?-1:1]]);
for(let q=0;q<36;q++)for(let z=0;z<S.length;z++)for(const [a,b,s] of pairs[q])for(let l=0;l<k;l++)if(B[b][l]&&!(S[z]&(1<<l)))rows[a*T.length+where.get(S[z]|(1<<l))][q*S.length+z]=(s*(pop[S[z]&((1<<l)-1)]%2?-1:1)*B[b][l]+101)%101;
let r=0;for(let c=0;c<rows[0].length&&r<rows.length;c++){let t=r;while(t<rows.length&&!rows[t][c])t++;if(t===rows.length)continue;[rows[r],rows[t]]=[rows[t],rows[r]]; const piv=rows[r],div=invs[piv[c]], ind=[];for(let j=c;j<piv.length;j++)if(piv[j]){piv[j]=(piv[j]*div)%101;ind.push(j);}for(let i=r+1;i<rows.length;i++){const row=rows[i], fac=101-row[c];if(fac===101)continue;for(const j of ind)row[j]=(row[j]+fac*piv[j])%101;}r++;}
return [r,wb(k-1,p).length,Math.ceil(r/wb(k-1,p).length)];}
const pop=new Uint8Array(1<<16); for(let i=1;i<pop.length;i++)pop[i]=pop[i>>1]+(i&1);
const invs=Array.from({length:101},(_,i)=>Array.from({length:101},(_,j)=>j).find(j=>(i*j)%101===1));let seed=1743; function rr(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>10)%101;}
for(let k=3;k<=9;k++) for(let p=1;p<=Math.floor(k/3);p++) {
  const B=Array.from({length:16},()=>Array.from({length:k},rr));
  if(k===9&&p===2) {
    const permanent=rank(B,p), determinant=rank(B,p,true);
    if(permanent[0]!==1141||determinant[0]!==1153||permanent[1]!==28||determinant[1]!==28) throw Error('certificate mismatch');
    console.log(JSON.stringify({B,permanent,determinant}));
  }
}