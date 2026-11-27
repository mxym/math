'use strict';
const p=17, R=Array.from({length:p},(_,i)=>i), mod=x=>(x%p+p)%p;
const inv=R.map(a=>R.find(b=>a*b%p===1));
const gcd=(a,b)=>b?gcd(b,a%b):a;
for(const cap of [9])for(let d=4;d<=7;d++){
 const X=R.slice(0,d+1), B=X.map(i=>{
  let g=[1],den=1;
  for(const j of X)if(j!==i){
   const h=Array(g.length+1).fill(0);
   for(let k=0;k<g.length;k++){h[k]=mod(h[k]-j*g[k]);h[k+1]=mod(h[k+1]+g[k]);}
   g=h;den=mod(den*(i-j));
  }
  return g.map(c=>mod(c*inv[den]));
 });
 const det=(i,j)=>mod(B[i][d-1]*B[j][d]-B[j][d-1]*B[i][d]);
 let r,s;
 outer:for(let i of X)for(let j of X)if(det(i,j)){r=i;s=j;break outer;}
 if(r===undefined)throw Error('interpolation coefficient rank');
 const D=inv[det(r,s)], free=X.filter(i=>i!==r&&i!==s), vals=new Uint8Array(p);
 const ev=R.map(x=>B.map(g=>mod(g.reduceRight((q,a)=>q*x+a,0))));
 const classes=gcd(d,p-1), mult=(p-1)/classes;
 let count=0,min=Infinity,max=0;
 // Modulus 17, primitive element 3. Argument dilation acts on the leading coefficient by d-th powers.
 if(3**8%p!==16)throw Error('primitive element');
 function visit(i,mass,squares,pen,top,lead){
  if(i<free.length){
   const j=free[i];
   for(let n=0;n<=cap&&mass+n<=51;n++){
    vals[j]=n;visit(i+1,mass+n,squares+n*n,pen+n*B[j][d-1],top+n*B[j][d],lead);
   }
   return;
  }
  const e=lead-top, a=mod(D*(-pen*B[s][d]-e*B[s][d-1]));
  const b=mod(D*(B[r][d-1]*e+B[r][d]*pen));
  if(a>cap||b>cap||mass+a+b>51)return;
  vals[r]=a;vals[s]=b;mass+=a+b;squares+=a*a+b*b;
  for(let j=d+1;j<p;j++){
   let z=0; for(let k=0;k<=d;k++)z+=vals[k]*ev[j][k];z%=p;
   if(z>cap||mass+z>51||mass+z+(p-1-j)*cap<51)return;
   mass+=z;squares+=z*z;
  }
  if(mass!==51)return;
  const w=(squares-153)/34;
  if(w<=0)throw Error('positive weight');
  count+=mult;min=Math.min(min,w);max=Math.max(max,w);
 }
 for(let i=0;i<classes;i++)visit(0,0,0,0,0,3**i%p);
 const countWant=[0,16,120,1712][d-4], maxWant=[0,4,5,6][d-4], minWant=[Infinity,4,2,1][d-4];
 if(count!==countWant||max!==maxWant||min!==minWant)throw Error('cap9 profiles');
 console.log({cap,d,count,min,max});
}

const W=429n,C=21n,Q=307n,p0=17n;
const ceil=(a,b)=>(a+b-1n)/b;
const assert=(v,s)=>{if(!v)throw Error(s)};
function envelope(min,cap){
 let best=0n;
 function part(n,s,lo,x){
  if(!n){if(!s&&x>best)best=x;return;}
  for(let v=lo;v<=cap&&v*n<=s;v++)part(n-1n,s-v,v,x+v*v);
 }
 for(let b=9n;b<=18n;b++)part(b,C,min,0n);
 return best;
}
const S6=envelope(2n,5n),S7=envelope(1n,6n);
assert(S6===57n&&S7===87n,'norm envelopes');
const diff=(N,S)=>{
 const den=p0*Q*(Q-N),num=W*W*p0*(Q-N)+(18n*W-C*Q)**2n*N;
 return C*num-S*W*den;
};
assert(ceil(9n*W,C)===184n,'support lower');
for(const [N,S] of [[198n,S6],[243n,S7]])assert(diff(N,S)>0n&&diff(N-1n,S)<=0n,'support upper');
for(const R of [8n,9n]){
 const N=ceil((R+2n)*W-(R-7n)*(16n-R)*5n,C);
 assert(N>=203n&&diff(N,S6)>0n,'high against sextic');
}
const min=(...x)=>x.reduce((a,b)=>a<b?a:b);
for(const mixed of [false,true]){
 let total=0,gap=null;
 for(let n=184n;n<=(mixed?242n:197n);n++)
 for(let m=mixed?184n:n;m<=197n;m++){
  const e=min(9n*m+(C*n-9n*W)/(mixed?1n:2n),9n*n+(C*m-9n*W)/2n,10n*m,...(mixed?[]:[10n*n]));
  const d=18n*n*m-Q*e,g=d*d-p0*n*m*(Q-n)*(Q-m);
  assert(d>0n&&g>0n,'unweighted polarity');
  total++;gap=gap===null||g<gap?g:gap;
 }
 assert(total===(mixed?826:105),'pair count');
 console.log({mixed,total,gap:gap.toString()});
}
