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
function solve(D,d){
 const M=Array.from({length:d+1},(_,j)=>D.map(([x,y])=>mod(x**(d-j)*y**j)));
 for(let j=0;j<=d;j++){
  const k=M.findIndex((u,i)=>i>=j&&u[j]);if(k<0)throw Error('dependence');
  [M[j],M[k]]=[M[k],M[j]];let u=iv[M[j][j]];M[j]=M[j].map(x=>mod(x*u));
  for(let k=0;k<=d;k++)if(k!==j){let u=M[k][j];M[k]=M[k].map((x,r)=>mod(x-u*M[j][r]));}
 }
 return M.map(a=>mod(-a[d+1])).concat(1);
}
function weight(C){
 let q=0,n=0,z=0;
 for(let t=0;t<p;t++){const v=C.reduceRight((s,x)=>(s*t+x)%p,0);n+=v;if(n>102)return -1;if(!v)z++;q+=v*(v-1)/2;}
 const l=(102-n)/p;if(!Number.isInteger(l)||l>z)return -1;
 const w=(q+136*l-255)/p;if(!Number.isInteger(w))throw Error('weight');
 return w;
}
function gcd(a,b){for(;b;){const r=a%b;a=b;b=r;}return a;}
for(const [d,min,lim] of [[4,4,225]]){
 const n=d+2,pat=[];
 function complete(k,ws,remain,lower){
  if(k===n){if(!remain&&ws.reduce((s,w)=>s+w*w,0)>lim)pat.push(ws);return;}
  for(let w=lower;w<=remain/(n-k);w++)complete(k+1,[...ws,w],remain-w,w);
 }
 complete(0,[],33,min);
 const Q=R.map(()=>Array.from({length:35},()=>[])),A=Array(d+1).fill(0);
 function gen(i){if(i<d-1){for(let t of R){A[i]=t;gen(i+1);}return;}const w=weight(A);if(w>=0)Q[A[d]][w].push(A.slice());}
 for(let a=1;a<p;a++){A[d]=a;gen(0);}
 const H=d*(d-1)/2, sums=pat.map(x=>({pattern:x,hits:0,tries:0,example:null})), masks=reps(n);
 for(const s of masks){
  const D=s.map(z=>F[z]),leading=solve(D,d);
  let scales=gcd(d,p-1);
  const vecs=D.map(([x,y])=>Array.from({length:d-1},(_,j)=>j).flatMap(j=>Array.from({length:j+1},(_,b)=>mod(x**(j-b)*y**b))));
  for(let l=0;l<scales;l++){
   const a=leading.map(z=>mod(z*3**l));
   const bank=a.map((u,i)=>Q[u].map(C=>C.map(c=>{let k=0;const f=[];
    for(let j=0;j<d-1;j++)for(let j2=0;j2<=j;j2++,k++)f[k]=mod(c[j]*vecs[i][k]);return {c,f};})));
   const w0=mod(6*(n-1));
   for(let h=0;h<n;h++)for(const out of sums){
    const q=out.pattern.at(-1), c={};for(const w of out.pattern.slice(0,-1))c[w]=(c[w]??0)+1;
    if(!Q[a[h]][q].length)continue;
    const pin=Array.from({length:d-1},(_,j)=>j*(j+1)/2+(D[h][0]?0:j));
    const sum=Array(H).fill(0),profiles=[];
    function loop(i){
     if(i===h){loop(i+1);return;}
     if(i===n){
      out.tries++;
      let r=pin.map(z=>mod((z===0?w0:0)-sum[z]));r.push(0,a[h]);
      for(let j=0,k=0;j<d-1;j++)for(let b=0;b<=j;b++,k++)if(mod(sum[k]+vecs[h][k]*r[j]-(k===0?w0:0)))return;
      if(weight(r)!==q)return;
      ++out.hits;out.example??={mask:s,h,profiles:profiles.slice(),r};return;
     }
     for(const k in c)if(c[k]){
      c[k]--;for(const {c:x,f} of bank[i][k]){for(let j=0;j<H;j++)sum[j]+=f[j];profiles.push(x);loop(i+1);profiles.pop();for(let j=0;j<H;j++)sum[j]-=f[j];}c[k]++;
     }
    }
    loop(0);
   }
  }
 }
 if(masks.length!==10||sums.length!==2||sums.some(x=>x.hits)||sums.map(x=>x.tries).sort((a,b)=>a-b).join()!=="8208,37728")throw Error("quartic census");
 console.log({d,lim,orbits:masks.length,output:sums});
}
