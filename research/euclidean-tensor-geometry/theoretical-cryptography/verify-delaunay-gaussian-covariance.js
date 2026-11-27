"use strict";
// Deterministic exact and numerical checks on small, generated root lattices.
let exact=0,numerical=0;
function check(ok,msg,numeric=false){if(!ok)throw new Error(msg);if(numeric)++numerical;else ++exact;}
function pop(x){let n=0;while(x){x&=x-1;++n;}return n;}
function weightedBinary(n,accept,w){
 const f=Array(n).fill(0n),s=Array.from({length:n},()=>Array(n).fill(0n));let Z=0n;
 for(let a=0;a<(1<<n);++a)if(accept(a)){
   let weight=1n;const I=[];
   for(let i=0;i<n;++i)if(a&(1<<i)){weight*=BigInt(w[i]);I.push(i);}
   Z+=weight;
   for(const i of I){f[i]+=weight;for(const j of I)s[i][j]+=weight;}
 }
 return {Z,f,V:s.map((r,i)=>r.map((x,j)=>x*Z-f[i]*f[j]))};
}
for(let n=2;n<=9;++n)for(let seed=0;seed<27;++seed){
 const w=Array.from({length:n},(_,i)=>1+((seed*seed+(seed+2)*i+3*i*i)%29));
 for(let k=0;k<=n;++k){
   const {Z,V}=weightedBinary(n,x=>pop(x)===k,w);
   for(let i=0;i<n;++i){
     check(V[i].reduce((a,b)=>a+b,0n)===0n,"fixed size covariance row sum");
     check(4n*V[i][i]<=Z*Z,"binary variance ceiling");
     for(let j=0;j<n;++j)if(i!==j)check(V[i][j]<=0n,"weighted fixed size negative dependence");
   }
 }
 for(let sign=0;sign<=1;++sign){
   const {Z,V,f}=weightedBinary(n,x=>pop(x)%2===sign,w);
   const means=w.map(x=>BigInt(x-1)), den=w.map(x=>BigInt(x+1));
   const prod=(a,skip=[])=>a.reduce((x,y,i)=>skip.includes(i)?x:x*y,1n);
   const parity=(n-sign)%2===0?1n:-1n; // product of spins s=2*b-1
   const den0=prod(den)+parity*prod(means);
   check(2n*Z===den0,"parity normalizing constant");
   for(let i=0;i<n;++i){
     const numerator=means[i]*prod(den,[i])+parity*den[i]*prod(means,[i]);
     check(2n*(2n*f[i]-Z)===numerator,"parity mean formula");
     let off=0n;
     for(let j=0;j<n;++j)if(j!==i){
       const a=V[i][j];off+=a<0n?-a:a;
       // This is the binary covariance numerator, equal to one fourth of the spin one.
       const covNumer=parity*(den[i]**2n-means[i]**2n)*(den[j]**2n-means[j]**2n)*prod(means,[i,j])*prod(den,[i,j]);
       check(16n*a===covNumer,"parity covariance numerator");
     }
     check(off<=V[i][i] && 4n*V[i][i]<=Z*Z,"absolute row sum controls parity covariance");
   }
 }
}
function det(M) {
 const n=M.length,a=M.map(r=>r.slice());let sign=1n, prev=1n;
 if(n===0)return 1n;
 for(let k=0;k<n-1;++k){
   let j=k;while(j<n && a[j][k]===0n)++j;if(j===n)return 0n;
   if(j!==k){[a[k],a[j]]=[a[j],a[k]];sign=-sign;}
   for(let i=k+1;i<n;++i)for(let j=k+1;j<n;++j)a[i][j]=(a[i][j]*a[k][k]-a[i][k]*a[k][j])/prev;
   prev=a[k][k];for(let i=k+1;i<n;++i)a[i][k]=0n;
 }
 return sign*a[n-1][n-1];
}
for(let n=2;n<=7;++n)for(let seed=0;seed<45;++seed){
 const q=Array.from({length:n},(_,i)=>BigInt(1+((3*i*i+seed*(i+7)+seed*seed)%41)));
 q[0]=q[0]**2n;
 const scale=q.reduce((a,b)=>a*b,1n), w=q.map(x=>scale*x),u=q.map(x=>scale/x);
 const Q=w.map((x,i)=>x+u[i]),b=w.map((x,i)=>x-u[i]),Z=Q.reduce((x,y)=>x+y,0n);
 const M=Q.map((x,i)=>Q.map((y,j)=>(i===j?Z*Z-2n*Z*x:0n)+2n*b[i]*b[j]));
 for(let S=1;S<(1<<n);++S){
   const idx=Q.map((_,i)=>i).filter(i=>S&(1<<i));
   check(det(idx.map(i=>idx.map(j=>M[i][j])))>=0n,"crosspolytope half-identity covariance PSD");
 }
}
for(let N=2;N<=8;++N)for(let S=1;S<(1<<N)-1;++S)for(let T=1;T<(1<<N)-1;++T){
 const k=pop(S),l=pop(T),gram=N*pop(S&T)-k*l,norm=l*(N-l);
 check(gram<=norm && (gram===norm)===(S===T),"A* exact pair midpoint");
 if((S&T)===S)check(gram===k*(N-l) && gram>0,"positive nested-layer cross term");
}

function tensor(n,fun) {
 const x=Array(n).fill(0);
 function visit(i){if(i===n){fun(x);return;}for(let j=-3;j<=3;++j){x[i]=j;visit(i+1);}}
 visit(0);
}
function norm(x){return Math.hypot(...x);}
function dot(x,y){return x.reduce((a,b,i)=>a+b*y[i],0);}
function thetaMoments(L,c,t) {
 const E=L.map(x=>x.reduce((a,b,j)=>a+(b-c[j])**2,0)), m=Math.min(...E);
 let Z=0, means=c.map(()=>0), second=c.map(()=>c.map(()=>0));
 for(let j=0;j<L.length;++j){
   const w=Math.exp(-t*(E[j]-m)), x=L[j]; Z+=w;
   for(let a=0;a<c.length;++a){
     means[a]+=w*x[a];
     for(let b=0;b<c.length;++b)second[a][b]+=w*x[a]*x[b];
   }
 }
 return second.map((r,i)=>r.map((a,j)=>a/Z-means[i]*means[j]/Z**2));
}
for(let n=2;n<=4;++n){
 const Z=[],D=[],A=[],T=[];
 tensor(n,x=>{Z.push(x.slice());if(x.reduce((a,b)=>a+b,0)%2===0)D.push(x.slice());});
 tensor(n,x=>{
   A.push([...x,-x.reduce((a,b)=>a+b,0)]);
   const y=[...x,0], m=y.reduce((a,b)=>a+b,0)/(n+1);T.push(y.map(q=>q-m));
 });
 const defs=[
   [Z,Array.from({length:n},(_,i)=>+(i===0))],
   [D,Array.from({length:n},(_,i)=>+(i<2))],
   [A,Array.from({length:n+1},(_,i)=>i===0?1:i===1?-1:0)],
   [T,Array.from({length:n+1},(_,i)=>+(i<Math.floor((n+1)/2))-Math.floor((n+1)/2)/(n+1))]
 ];
 for(const [L,y] of defs){
   const d=norm(y),u=y.map(x=>x/d), center=y.map(x=>x/2);
   for(let seed=0;seed<7;++seed)for(const t of [80,112,160]){
     const h=y.map((_,i)=>((i*3+seed*7)%11-5)/5), c=center.map((x,i)=>x+h[i]/(2*t));
     const V=thetaMoments(L,c,t),v=dot(u,V.map(r=>dot(r,u)));
     const p=1/(1+Math.exp(-dot(h,y)));
     check(Math.abs(v-d*d*p*(1-p))<3e-6,"tilted exact-pair scaling "+[n,seed,t,v,d*d*p*(1-p)],true);
   }
 }
}
console.log(JSON.stringify({exact,numerical}));
