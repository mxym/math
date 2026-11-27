'use strict';
const p=17, R=Array.from({length:p},(_,i)=>i), mod=x=>(x%p+p)%p;
const inv=R.map(a=>R.find(b=>a*b%p===1));
const gcd=(a,b)=>b?gcd(b,a%b):a;
for(const cap of [9,12])for(let d=4;d<=7;d++){
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
   for(let n=0;n<=cap&&mass+n<=68;n++){
    vals[j]=n;visit(i+1,mass+n,squares+n*n,pen+n*B[j][d-1],top+n*B[j][d],lead);
   }
   return;
  }
  const e=lead-top, a=mod(D*(-pen*B[s][d]-e*B[s][d-1]));
  const b=mod(D*(B[r][d-1]*e+B[r][d]*pen));
  if(a>cap||b>cap||mass+a+b>68)return;
  vals[r]=a;vals[s]=b;mass+=a+b;squares+=a*a+b*b;
  for(let j=d+1;j<p;j++){
   let z=0; for(let k=0;k<=d;k++)z+=vals[k]*ev[j][k];z%=p;
   if(z>cap||mass+z>68||mass+z+(p-1-j)*cap<68)return;
   mass+=z;squares+=z*z;
  }
  if(mass!==68)return;
  const w=(squares-272)/34;
  if(!Number.isInteger(w)||w<1)throw Error('positive integer weight');
  count+=mult;min=Math.min(min,w);max=Math.max(max,w);
 }
 for(let i=0;i<classes;i++)visit(0,0,0,0,0,3**i%p);
 const want=cap===9?[[12,4],[64,4],[1360,6],[21920,6]]:[[56,8],[560,9],[10048,10],[171472,11]];
 if(count!==want[d-4][0]||max!==want[d-4][1])throw Error('profile catalogue');
 console.log({cap,d,count,min,max});
}
