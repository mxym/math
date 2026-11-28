#!/usr/bin/env node
// Complete fixed-grid certificate for five spherical points on one affine circle.
'use strict';
const K=256,B=65536,D=10000000;
const piL=3141592653589793n,piU=piL+1n,unit=1000000000000000n,denA=3n*BigInt(K)*unit;
const low=[],high=[];const fact=n=>n<2?1n:BigInt(n)*fact(n-1);const d=denA,dd=d*d,scale=fact(26)*d**26n;
// Machin's identity and alternating arctangent-series brackets.
const sum=(x,y)=>[x[0]*y[1]+y[0]*x[1],x[1]*y[1]], sc=(k,x)=>[k*x[0],x[1]], cmp=(x,y)=>x[0]*y[1]-y[0]*x[1];
function atan(q){let x=[0n,1n];for(let i=0;i<16;i++)x=sum(x,[(i%2?-1n:1n),BigInt(2*i+1)*q**BigInt(2*i+1)]);return [x,sum(x,[1n,33n*q**33n])];}
const [l5,h5]=atan(5n),[l239,h239]=atan(239n);
if(cmp(sum(sc(16n,l5),sc(-4n,h239)),[piL,unit])<=0n||cmp(sum(sc(16n,h5),sc(-4n,l239)),[piU,unit])>=0n)throw Error('pi bracket');
for(let n=0n;n<=4n;n++){let d=10n,r=d-n;
 let u=72n*n**4n+216n*n*n*r*r+27n*r**4n-18n*n*n*d*d-9n*r*r*d*d+8n*n*r**3n+32n*n*r*(7n*n*n-6n*n*d+5n*d*d/2n)-18n*d**4n;
 if(u!==n*(83n*n**3n-100n*n*n*d+55n*n*d*d-2n*d**3n))throw Error('polynomial');}
if(83n+55n*32n**2n>=2n*32n**3n)throw Error('small heights');
let cf=Array.from({length:14},(_,k)=>(k%2?-1n:1n)*fact(26)/fact(2*k)*d**BigInt(26-2*k)), div=(a,b)=>a>=0n?a/b:-((-a+b-1n)/b);
for(let j=0;j<=3*K;j++){let zj=BigInt(j), xl=(zj*piL)**2n,xu=(zj*piU)**2n,lo=0n,hi=0n;
 for(let k=13;k>=0;k--)lo=lo*xu+cf[k];
 for(let k=12;k>=0;k--)hi=hi*xl+cf[k];
 low[j]=Math.max(-B,Number(div(lo*BigInt(B),scale)));high[j]=Math.min(B,-Number(div(-hi*BigInt(B),scale)));}
const f=[],g=[],dg=[];for(let i=0;i<=B;i++){let x=BigInt(i),b=BigInt(B),n=BigInt(D)*(4n*x**4n-x*x*b*b);f[i]=-Number(div(-n,4n*b**4n));}

const U=960,N=5,c=[0,1,2,3,4],iu=Array.from({length:5},(_,i)=>i);
let n=0,acc=0,empty=0,minmargin=Infinity,depth=0,cases=0;
const ub=(l,h,ul,uh)=>{
 let v=Math.floor((ul*B+(U-ul)*low[h])/U),w=Math.ceil((uh*B+(U-uh)*high[l])/U);
 return Math.max(f[Math.abs(v)],f[Math.abs(w)],v<=0&&w>=0?0:-Infinity);
};
const perms=c.flatMap(r=>[1,-1].map(s=>c.map(i=>(r+s*i+10)%5)));let ord=[],grp=perms;
for(let i of c){for(let j of new Set(grp.map(g=>g[i])))if(i!==j)ord.push([i,j]);grp=grp.filter(g=>g[i]===i);}
function go(l,h,ul,uh,dep){n++;depth=Math.max(depth,dep);
 for(let pass=0;pass<12;pass++){let ch=false,lo=l.reduce((a,b)=>a+b,0),hi=h.reduce((a,b)=>a+b,0);
 if(lo>K||hi<K){empty++;return;}
 for(let i of c){let L=Math.max(l[i],K-hi+h[i]),H=Math.min(h[i],K-lo+l[i]);if(L>H){empty++;return;}if(l[i]!=L||h[i]!=H){l[i]=L;h[i]=H;ch=true;}}
 for(let [i,j]of ord){if(l[i]>h[j]){empty++;return;}if(h[i]>h[j]){h[i]=h[j];ch=true;}if(l[j]<l[i]){l[j]=l[i];ch=true;}}
 if(!ch)break;}
 let tot=5*3*D/4;
 for(let i of c){let j=(i+1)%5;tot+=2*ub(K+l[i],K+h[i],ul,uh);
 let hi=Math.min(K,h[i]+h[j],K-l[(i+2)%5]-l[(i+3)%5]-l[(i+4)%5]),lo=Math.max(l[i]+l[j],K-h[(i+2)%5]-h[(i+3)%5]-h[(i+4)%5]);
 if(lo>hi){empty++;return;}tot+=2*ub(2*K+lo,2*K+hi,ul,uh);}
 if(tot<25*D/4){acc++;minmargin=Math.min(minmargin,25*D/4-tot);return;}
 let w=h.map((x,i)=>x-l[i]>1?(x-l[i])/K:0).concat(uh-ul>1?4*(uh-ul)/U:0),k=w.indexOf(Math.max(...w));
 if(!w[k])throw Error(JSON.stringify([l,h,ul,uh,tot]));
 if(k===5){let m=(ul+uh)>>1;go(l.slice(),h.slice(),ul,m,dep+1);go(l,h,m,uh,dep+1);}
 else{let m=(l[k]+h[k])>>1,L=l.slice(),H=h.slice();L[k]=H[k]=m;go(l.slice(),H,ul,uh,dep+1);go(L,h.slice(),ul,uh,dep+1);}}
go(Array(5).fill(0),Array(5).fill(K),30,320,0);if(n!==2003||acc!==980||empty!==22||minmargin!==5532)throw Error('census');console.log('PASS',{n,acc,empty,minmargin,depth});
