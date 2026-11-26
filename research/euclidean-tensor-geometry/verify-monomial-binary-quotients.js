'use strict';
const as=s=>parseInt(s,2);
const mul=(x,y)=>{let z=0;while(y){if(y&1)z^=x;x<<=1;y>>=1;}return z};
const deg=x=>31-Math.clz32(x);
const red=(x,y)=>{while(x&&deg(x)>=deg(y))x^=y<<(deg(x)-deg(y));return x;};
function assert(x,m){if(!x)throw Error(m)}
const rev=(p,d)=>{let s=0;for(let j=0;j<=d;j++)if((p>>j)&1)s|=1<<(d-j);return s;};
function run(f,p,pstar,emin,emax,ecol){
 const A=as(p),B=as(pstar),r=deg(A),q=1<<r,n=q-1;
 const mask=f.reduce((z,c,i)=>z|((c&1)<<i),0);
 assert(A!==B&&mul(A,B)===mask&&rev(A,r)===B,'binary product/reciprocity');
 const P=Array(n).fill(0);
 for(let x=1,i=0;i<n;i++){
  P[i]=x;x=red(x<<1,A);
  if(i<n-1)assert(x!==1,'shorter period');else assert(x===1,'bad cycle');
 }
 assert(!P.includes(0)&&new Set(P).size===n,'all nonzero elements');
 const m=(x,y)=>red(mul(x,y),A);
 const trace=Array.from({length:q},(_,z)=>{
  let t=0;for(let j=0;j<r;j++){t^=z;z=m(z,z);}
  assert(t===0||t===1,'trace');return t;
 });
 const hist={};let min=Infinity,max=-Infinity,witness=0;
 for(let a=1;a<q;a++){
  let v=0;for(let i=0;i<n;i++)v+=1-2*trace[P[i]^m(a,P[(n-i)%n])];
  hist[v]=(hist[v]||0)+1;if(v<min){min=v;witness=a;}max=Math.max(max,v);
 }
 const colors=Math.ceil(1+n/-min);
 assert(min===emin&&max===emax&&colors===ecol,'spectral values');
 return {degree:2*r,factors:[p,pstar],min,max,witness,colors,hist};
}
// Coefficients are low-to-high. The first polynomial is a representative of
// the exceptional parity class; only its binary reduction is used.
const rows=[
 run([1,0,4,1,3,0,-4,-1,-7,-1,-4,0,3,1,4,0,1], '101001101','101100101',-29,31,10),
 run([1,1,1,1,0,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,0,1,1,1,1],
     '10100100011','11000100101',-61,63,18),
];
console.log(JSON.stringify(rows,null,2));
