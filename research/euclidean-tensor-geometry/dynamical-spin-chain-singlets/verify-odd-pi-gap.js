// Numerical supplementary checks (ordinary double precision); analytic proofs do not use these.
const assert=(b,msg)=>{if(!b)throw Error(JSON.stringify(msg));};
function mineig(M){
 const n=M.length;
 function pos(x){const L=Array.from({length:n},()=>Array(n).fill(0));
  for(let i=0;i<n;i++)for(let j=0;j<=i;j++){
    let y=M[i][j]-(i===j?x:0);for(let k=0;k<j;k++)y-=L[i][k]*L[j][k];
    if(i===j){if(!(y>0))return false;L[i][i]=Math.sqrt(y);}else L[i][j]=y/L[j][j];
  }return true;
 }
 let a=0,b=Math.min(...M.map((r,i)=>r[i]))+1;
 for(let i=0;i<42;i++){const c=(a+b)/2;if(pos(c))a=c;else b=c;}return(a+b)/2;
}
function raw(n,z){
 const tt=z*z-1,c=z*z+1,S=new Map;
 for(let i=0;i<3**n;i++){let x=i,w=[];for(let j=0;j<n;j++){w.push(x%3);x=x/3|0;}const k=w.filter(x=>x===1).length,h=w.filter(x=>x===2).length;
 if(h===0&&(k===0||k===n))continue;const key=h+":"+k;let a=S.get(key);if(!a)S.set(key,a=[]);a.push([i,w]);}
 let best=[Infinity,null];
 for(const [key,A] of S){
 const idx=new Map(A.map((p,i)=>[p[0],i])),M=A.map(()=>Array(A.length).fill(0));
 A.forEach(([i,w],j)=>{
  for(let a=0;a<n;a++){const b=(a+1)%n;const u=w[a],v=w[b];let d=0,p=0;
   if(u===2&&v===2)d=2*c;else if(u===2||v===2){d=c;p=a===n-1?tt:-tt;}
   else if(u!==v){d=(u===0?z-1:z+1)**2;p=tt;}
   M[j][j]+=d;if(p)M[j][idx.get(i+(v-u)*3**a+(u-v)*3**b)]+=p;
  }
 });
 const x=mineig(M);if(x<best[0])best=[x,key];
 }
 return best;
}
function cycle(n,z){
 const l=n-1,M=Array.from({length:l},()=>Array(l).fill(0)),t=z*z-1;
 for(let i=0;i<l;i++)M[i][i]=i===0?6+2*z:i===l-1?6-2*z:8;
 function edge(i,j,w){M[i][i]+=w*t;M[j][j]+=w*t;M[i][j]-=w*t;M[j][i]-=w*t;}
 for(let i=0;i<l-1;i++)edge(i,i+1,2);edge(0,l-1,1);
 return mineig(M);
}
let exact3=0, weak=0, strong=0;
for(const z of [1.001,1.1,Math.sqrt(9/5),2,4,-8,40]){
 const u=z*z,ex=Math.min(u+3,3*(u+1)-Math.sqrt(4*u+9*(u-1)**2));
 assert(Math.abs(raw(3,z)[0]-ex)<1e-7,[z,raw(3,z),ex]);exact3++;
}
for(const n of [3,5,7]){
 const z=Math.sqrt(1.003), pure=4+2*(z*z-1)*(1-Math.cos(Math.PI/n));
 assert(Math.abs(raw(n,z)[0]-pure)<1e-7,[n,z,raw(n,z),pure]);weak++;
 for(const z of [8,20,40]){
  const a=raw(n,z), b=cycle(n,z);assert(Math.abs(a[0]-b)<2e-7,[n,z,a,b]);strong++;
  console.log(JSON.stringify({n,z,gap:a[0],sector:a[1],cycle:b}));
 }
}
let uniform=0;
for (const n of [5,7]) for (const t of [0.05,0.25,0.5,0.8,1]) {
 const z=Math.sqrt(1+t), a=raw(n,z), b=4+2*t*(1-Math.cos(Math.PI/n));
 assert(Math.abs(a[0]-b)<1e-8,[n,t,a,b]);uniform++;
}
console.log(JSON.stringify({exact3,weak,strong,uniform}));
