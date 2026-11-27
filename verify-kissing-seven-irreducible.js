'use strict';
// Standard Node.js; every branch test uses integers. --alternate uses a second grid
// and tie ordering. Math.sqrt only proposes an integer checked before use.
const assert=require('node:assert/strict'),alt=process.argv.includes('--alternate');
const S=alt?16384:8192,S2=S*S,R=7*(alt?1536:1024),B=alt?768:1024,L=256,M=3*B/2;
const floor=(n,d)=>Math.floor(n/d); // used on nonnegative safe integers incl. exact multiples
function isq(n){let i=Math.floor(Math.sqrt(Math.max(0,n)));while((i+1)**2<=n)i++;while(i*i>n&&i>0)i--;return i}
function ceilsq(n){if(n<=0)return 0;let i=isq(n);return i*i===n?i:i+1}
const C=ceilsq(7*S2/4);
const fields=[1];while(fields.length<7){let a=2*fields.at(-1);fields.push(a>=8?a^11:a)}
function par(x){return ((x>>2)^(x>>1)^x)&1}
const sign=[-1,1,1,1,1,1,1],H=Array.from({length:8},(_,h)=>fields.map((a,i)=>sign[i]*(1-2*par(a&h))));
const masks=Array.from({length:7},(_,s)=>fields.map(a=>par(a&(s+1))));
const G=[];for(let k=0;k<=3;k++)for(let w=k?0:1;w<8;w++)G.push({k,m:k?2:1,s:fields.map((a,i)=>sign[i]*sign[(i+k)%7]*(1-2*par(a&w)))});
assert.equal(G.reduce((a,g)=>a+g.m,0),55);
const sf=new Int16Array(M),tab=new Int16Array(M*M),b=BigInt(B);
for(let i=0;i<M;i++){
 let a=BigInt(i-B),e=a+1n;
 function dist(p,q){let l=a*q+p*b,r=-(e*q+p*b);return l>0n?l:r>0n?r:0n}
 let num=BigInt(L)*22n*(b/2n-e)*(4n*a+13n*b)*dist(127n,200n)**2n*dist(1n,10n)**2n;
 let den=4n*200n**2n*10n**2n*b**6n;
 sf[i]=Number(num/den);assert(sf[i]>=0&&sf[i]<32767);
}
for(let i=0;i<M;i++){let u=32767;for(let j=i;j<M;j++)tab[i*M+j]=u=Math.min(u,sf[j])}
const binMax=sf.reduce((a,b)=>Math.max(a,b),0);
for(const v of [1112*8*R*R*L,7*5405*L*(R*R/2),7*8*R*R*55*binMax,7*S*7*S*R])
 assert(Number.isSafeInteger(v));
let nodes,maxDepth;
function test(lo,hi,axis,depth){
 nodes++;maxDepth=Math.max(maxDepth,depth);assert(depth<=80);
 for(let pass=0;pass<2;pass++){
  for(let i=0;i<7;i++){let l=0,u=0;for(let j=0;j<7;j++)if(j!==i){l+=lo[j]**2;u+=hi[j]**2}
   if(l>S2)return 0;lo[i]=Math.max(lo[i],isq(Math.max(0,S2-u)));hi[i]=Math.min(hi[i],ceilsq(S2-l),hi[axis]);if(lo[i]>hi[i])return 0;
  }
  for(let mask of masks){let u=0;for(let i=0;i<7;i++)if(mask[i])u+=hi[i]**2;if(4*u<S2)return 0;
   for(let i=0;i<7;i++)if(mask[i])lo[i]=Math.max(lo[i],isq(Math.max(0,S2/4-u+hi[i]**2)));
  }
  for(let w of H){let l=0,u=0;for(let i=0;i<7;i++){l+=w[i]>0?lo[i]:-hi[i];u+=w[i]>0?hi[i]:-lo[i]}
   if(l>C||u< -C)return 0;
   for(let i=0;i<7;i++){let a=lo[i],b=hi[i];if(w[i]>0){hi[i]=Math.min(b,a+C-l);lo[i]=Math.max(a,b-C-u)}
    else{lo[i]=Math.max(a,b+l-C);hi[i]=Math.min(b,a+C+u)}}
  }
  for(let i=0;i<7;i++)if(lo[i]>hi[i])return 0;
 }
 let rem=8*R/7,U=0,intervals=[];
 for(let w of H){let l=0,u=0;for(let i=0;i<7;i++){l+=w[i]>0?lo[i]:-hi[i];u+=w[i]>0?hi[i]:-lo[i]}
  let a=floor(R*Math.max(0,l,-u)**2,7*S2),b=Math.min(R/4,Math.ceil(R*Math.max(l*l,u*u)/(7*S2)));
  if(a>b)return 0;rem-=a;U+=a*a;intervals.push([a+b,b-a]);
 }
 if(rem<0)return 0;intervals.sort((a,b)=>b[0]-a[0]);
 for(let [s,w]of intervals){let z=Math.min(w,rem);U+=s*z;rem-=z}
 if(rem)return 0;
 const target=7*5405*L*U-1112*8*R*R*L,unit=7*8*R*R;let bonus=0;
 if(target<0)return 1;
 for(let g of G){
  let l=0,u=0;
  if(!g.k){let la=0,ua=0,lb=0,ub=0;
   for(let i=0;i<7;i++)if(g.s[i]<0){la+=lo[i]**2;ua+=hi[i]**2}else{lb+=lo[i]**2;ub+=hi[i]**2}
   l=Math.max(S2-2*ua,2*lb-S2);u=Math.min(S2-2*la,2*ub-S2);
  }else for(let i=0;i<7;i++){let j=(i+g.k)%7,a=lo[i]*lo[j],b=hi[i]*hi[j];l+=g.s[i]>0?a:-b;u+=g.s[i]>0?b:-a}
  if(2*l>S2)return 0;
  let i=Math.max(0,Math.min(M-1,Math.floor((l+S2)*B/S2))),j=Math.max(0,Math.min(M-1,Math.floor((u+S2)*B/S2)));
  if(i<=j)bonus+=g.m*tab[i*M+j];
  if(bonus*unit>target)return 1;
 }
 let j=-1,width=0;
 for(let k=0;k<7;k++){let i=alt?6-k:k;if(i!==axis&&hi[i]-lo[i]>width){j=i;width=hi[i]-lo[i]}}
 assert(width>=2,'unresolved integer cell');let c=Math.floor((lo[j]+hi[j])/2),L0=lo.slice(),H0=hi.slice();H0[j]=c;L0[j]=c;
 test(lo.slice(),H0,axis,depth+1);test(L0,hi.slice(),axis,depth+1);
}
for(let axis of [0,1,3]){
 let a=Array(7).fill(0),b=Array(7).fill(ceilsq(5*S2/8));a[axis]=isq(Math.floor(S2/7));nodes=0;maxDepth=0;
 test(a,b,axis,0);console.log('axis',axis,'nodes',nodes,'depth',maxDepth);
}
