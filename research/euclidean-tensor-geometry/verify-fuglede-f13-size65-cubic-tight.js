'use strict';
const P=13, r=Array.from({length:P},(_,i)=>i), mod=x=>(x%P+P)%P;
const inv=r.map(a=>r.find(b=>mod(a*b)===1));
const assert=(b,s)=>{if(!b)throw Error(s);};
const data=r.map(()=>r.map(()=>r.map(()=>null))), lists=r.map(()=>[]), hist={};
for(let a=1;a<P;a++)for(let b of r)for(let c of r){
  let f=r.map(x=>mod(a*x**3+b*x+c)), z=f.filter(v=>!v).length;
  let k=(65-f.reduce((s,v)=>s+v,0))/13;
  if(k%1||k<0||k>z)continue;
  let w=(f.reduce((s,v)=>s+v*(v-1)/2,0)+78*k-130)/13;
  assert(w>=3&&Number.isInteger(w),"bad cubic weight");
  hist[w]=(hist[w]||0)+1;
  if(w<=8){let x={b,c,w,k,z};data[a][b][c]=x;lists[a].push(x);}
}
assert(JSON.stringify(hist)===JSON.stringify({3:20,4:24,5:72,6:156,7:120,8:132,9:36,10:48,11:4}),"cubic profile census");
const byB=lists.map(L=>r.map(b=>L.filter(x=>x.b===b)));
const choose=(n,k)=>{let a=1;for(let i=1;i<=k;i++)a=a*(n-i+1)/i;return a;};
let masks=0,leads=0,patterns={};
for(let s=2;s<P;s++)for(let t=s+1;t<P;t++){
  masks++;
  let u=inv[mod(s*s-s)],v=inv[mod(t-s)];
  for(let a4=1;a4<P;a4++){
    const a3=mod((t-t*t)*a4*u),a2=mod(-s*a3-t*a4);
    const a0=mod(-a2-a3-a4),a1=mod(-a2-a3*s**3-a4*t**3);
    if(!a0||!a1||!a2||!a3)continue;
    leads++;
    for(const x of lists[a0])for(const y of lists[a1]){
      if(x.w+y.w>11)continue;
      for(const z of lists[a2]){
        let w=x.w+y.w+z.w;
        if(w>14)continue;
        const sx=-x.b-z.b,sy=-y.b-z.b,b4=mod((sy-s*sx)*v),b3=mod(sx-b4),c3=20-x.c-y.c-z.c;
        for(const q of byB[a3][b3]){
          if(w+q.w>17)continue;
          const f=data[a4][b4][mod(c3-q.c)];
          if(!f||w+q.w+f.w!==20)continue;
          const A=[x,y,z,q,f], k=A.map(o=>o.w).sort((a,b)=>a-b).join();
          const H=patterns[k]??=[0,0]; H[0]++; H[1]+=A.reduce((n,o)=>n*choose(o.z,o.k),1);
        }
      }
    }
  }
}
assert(masks===55&&leads===660,"cubic pencil coordinates");
assert(Object.keys(patterns).length===2&&patterns["3,3,4,4,6"]?.join()==="1800,1800"&&patterns["3,3,3,3,8"]?.join()==="360,600","cubic tight-pattern census");
const n=14*410**2-8200*183;
assert(n>0&&n*n>13*(2132*183-410**2)**2,"weighted polarity mixing");
console.log({hist,masks,leads,patterns});
