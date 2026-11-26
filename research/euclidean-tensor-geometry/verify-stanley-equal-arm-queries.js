// Check decorated-spider cut-query identities at exact modular evaluations.
// Node.js, no packages. Unit profiles at two independently assigned nonzero evaluations.
'use strict';
const p=1009, mul=(a,b)=>a*b%p;
function add(a,b){return (a+b)%p;}
function pow(x,n){let y=1;while(n-- >0)y=mul(y,x);return y;}
function assert(x,m){if(!x)throw Error(m);}
let forests=0,queries=0;
for(let d=3;d<=5;d++)for(let L=1;L<=3;L++){
 const n=d*L+1, values=Array.from({length:n},(_,i)=>[(11+19*i+d+3*L)%p,(13+23*i+3*d+L)%p]);
 const all=values.reduce((v,w)=>mul(v,w[0]),1);
 const G=[], tail=Array.from({length:d},()=>[1]);
 for(let a=0;a<d;a++){
   let g=1;for(let j=L;j>=1;j--){const v=values[a*L+j];g=mul(g,v[0]);tail[a].push(mul(tail[a].at(-1),v[1]));}G.push(g);
 }
 function elem(r,omit=-1){
   const e=Array(r+1).fill(0);e[0]=1;
   for(let a=0;a<d;a++)if(a!==omit)for(let j=r;j>=1;j--)e[j]=add(e[j],mul(G[a],e[j-1]));
   return e[r];
 }
 const E=Array(d).fill(0), H=Array.from({length:L+1},()=>Array(d-1).fill(0));
 let inv=0;
 for(let mask=0;mask<(1<<(n-1));mask++){
   forests++;
   let center=1, centerU=values[0][0], other=[];
   for(let a=0;a<d;a++){
     let start=0,u=1,t=1;
     for(let j=1;j<=L;j++){
       const edge=a*L+j-1;
       if(mask&(1<<edge)){
         if(start===0){center+=j-1;centerU=mul(centerU,u);}
         else other.push([j-start,u,t]);
         start=j;u=t=1;
       }
       u=mul(u,values[edge+1][0]);t=mul(t,values[edge+1][1]);
     }
     if(start===0){center+=L;centerU=mul(centerU,u);}
     else other.push([L+1-start,u,t]);
   }
   if(center<=L)continue;
   const r=other.length;
   if(r>=1&&r<d&&other.every(x=>x[0]===L)){
     const pr=other.reduce((t,x)=>mul(t,x[1]),1);E[r]=add(E[r],pr);
     if(r===1)inv=add(inv,mul(centerU,pow(all,p-2)));
   }
   if(r>=1&&r<=d-1){
     for(let s=0;s<r;s++)if(other.every((x,j)=>j===s||x[0]===L)){
       const [len,,t]=other[s];let v=t;
       for(let j=0;j<r;j++)if(j!==s)v=mul(v,other[j][1]);
       H[len][r-1]=add(H[len][r-1],v);
     }
   }
 }
 for(let r=1;r<d;r++){queries++;assert(E[r]===elem(r),'elementary probe');}
 queries++;assert(mul(inv,elem(d))===elem(d-1),'reciprocal probe');
 for(let r=0;r<=d-2;r++)for(let l=1;l<=L;l++){
   let v=0;for(let a=0;a<d;a++)v=add(v,mul(tail[a][l],elem(r,a)));
   queries++;assert(v===H[l][r],'tail alignment probe');
 }
}
console.log(JSON.stringify({spiders:9,forests,queries}));
