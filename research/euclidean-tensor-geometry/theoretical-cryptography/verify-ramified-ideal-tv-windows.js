"use strict";
// Finite synthetic code-polynomial and Gaussian profile identities.
let exact=0,num=0;
function ck(x,m){if(!x)throw new Error(m);++exact;}
function near(a,b,t,m){
 if(!Number.isFinite(a)||!Number.isFinite(b)||Math.abs(a-b)>t*Math.max(1,Math.abs(a),Math.abs(b)))
   throw new Error(m+": "+a+" vs "+b);
 ++num;
}
function parity(x){
 x^=x>>>16; x^=x>>>8;x^=x>>>4;return (0x6996>>>(x&15))&1;
}
function gens(n,j){
 let f=1;for(let k=0;k<j;k++)f^=f<<1;
 return Array.from({length:n-j},(_,i)=>f<<i);
}
const words=G=>G.reduce((a,v)=>a.concat(a.map(x=>x^v)),[0]);
function dual(n,G){
 const w=[];
 for(let x=0;x<1<<n;x++)if(G.every(v=>parity(v&x)===0))w.push(x);
 return w;
}
function codeNum(C,x,q){
 let p=0n;
 for(const w of C){
  let s=1n;
  for(let k=0;k<x.length;k++)s*=((w>>k)&1)?x[k]:q;
  p+=s;
 }
 return p;
}
const minPow=j=>{let d=1;while(d<j)d*=2;return d;};
for(const n of [1,2,4,8,16])for(let j=0;j<=n;j++){
 const G=gens(n,j),C=words(G),T=dual(n,G),S=new Set(C);
 ck(C.length===S.size && C.length*T.length===1<<n,"code and dual dimensions");
 const q=19n,x=Array.from({length:n},(_,i)=>BigInt((i*i+3*j*i+5*j+2)%9-4));
 const value=codeNum(C,x,q);
 let avg=0n;
 for(const w of T)avg+=x.reduce((x0,v,i)=>x0*(q+(((w>>i)&1)?-v:v)),1n);
 ck(avg===BigInt(T.length)*value,"dual sign average equals code polynomial");
 if(j===0)continue;
 const B=minPow(j),H=n/B,R=words(gens(B,j)),Rset=new Set(R);
 const groups=[];
 for(let b=0;b<B;b++){
   const out=[0n,0n];
   for(let w=0;w<1<<H;w++){
    let m=1n;
    for(let k=0;k<H;k++)m*=((w>>k)&1)?x[b+k*B]:q;
    out[parity(w)]+=m;
   }
   groups.push(out);
 }
 let fromGroup=0n;
 for(const w of R)
  fromGroup+=groups.reduce((s,p,i)=>s*p[(w>>i)&1],1n);
 ck(fromGroup===value,"exact even-odd block polynomial factorization");
 for(const c of C) {
  let w=0;for(let k=0;k<n;k++)if((c>>k)&1)w^=1<<(k%B);
  ck(Rset.has(w),"parity remainder in residual code");
 }
 for(const eta of T){
   const ee=eta&((1<<B)-1);
   const rep=Array.from({length:H},(_,i)=>ee<<(i*B)).reduce((a,b)=>a^b,0);
   ck(rep===eta,"dual signs constant in residue groups");
 }
 if(j>=n/2&&n>=2){
  const H=n/2,shift=1<<H,rep=new Set(words(gens(H,j-H)).map(x=>x*(1+shift)));
  ck(rep.size===C.length&&C.every(v=>rep.has(v)),"repeated halves");
 }
 if(j<=n/2){
   let weight2=0;
   for(let u=0;u<n;u++)for(let v=u+1;v<n;v++){
     const yes=S.has((1<<u)^(1<<v));ck(yes===((v-u)%B===0),"weight-two location");
     if(yes)++weight2;
   }
   ck(weight2===B*H*(H-1)/2,"common shortest shell");
 }
}
const choose=(n,k)=>{
 let a=1n;
 for(let j=1;j<=k;j++)a=a*BigInt(n-j+1)/BigInt(j);
 return a;
};
for(let H=1;H<=12;H++)for(const p of [1n,2n,4n,7n]){
 const q=17n, N=1<<H;
 let mean0=0n,sq0=0n;
 for(let w=0;w<N;w++){
   let a=1n,b=1n;
   for(let j=0;j<H;j++){
    const s=((w>>j)&1)?p:-p;a*=q+s;b*=q-s;
   }
   if((a+b)%2n!==0n)throw new Error("even subset numerator");
   const m=(a+b)/2n; mean0+=m;sq0+=m*m;
 }
 ck(mean0===BigInt(N)*q**BigInt(H),"even-group mean is one");
 let v=0n;
 for(let j=0;j<=H;j+=2)v+=choose(H,j)*p**BigInt(2*j)*q**BigInt(2*(H-j));
 ck(sq0===BigInt(N)*v,"exact even-group second moment");
}
for(const T of [.04,.2,.7,1.8,3.2])for(let k=1;k<=47;k++){
  const a=Math.sqrt(T/2)*Math.abs(Math.sin(k*.03)),
        b=Math.sqrt(T/2)*Math.abs(Math.cos(k*1.18));
  const ref=Math.exp(-T/2)*Math.cosh(a)*Math.cosh(b),
        ctl=Math.exp(-T/2)*(Math.cosh(a+b)+Math.cosh(a-b))/2;
  near(ref,ctl,2e-13,"cosh comparison conditional mean");
  for(const g of [.5,.8,1.0,1.4,2.1]){
    const e=Math.abs(g*ref-1),
          f=(Math.abs(g*Math.exp(-T/2)*Math.cosh(a+b)-1)
             +Math.abs(g*Math.exp(-T/2)*Math.cosh(a-b)-1))/2;
    if(e>f+1e-13)throw new Error("conditional convex comparison");
    ++num;
  }
}
console.log(exact+" exact code and moment checks; "+num+" deterministic numerical checks: PASS");
