// Node.js independent checks; no proof relies on these experiments.
(()=>{const p=1009,md=z=>(z%p+p)%p;
function invM(z){let v=1,k=p-2;while(k){if(k&1)v=md(v*z);z=md(z*z);k>>=1;}return v;}
function rk(A,n){let k=0;for(let j=0;j<n&&k<A.length;j++){let i=k;while(i<A.length&&!A[i][j])i++;if(i===A.length)continue;[A[i],A[k]]=[A[k],A[i]];const z=invM(A[k][j]);for(let h=j;h<n;h++)A[k][h]=md(A[k][h]*z);for(let i=k+1;i<A.length;i++){const t=A[i][j];if(!t)continue;for(let h=j;h<n;h++)A[i][h]=md(A[i][h]-t*A[k][h]);}k++;}return k;}
function contract(v){
 const n=v.length,P=[0];v.forEach(x=>P.push(P.at(-1)+x));
 const M={};
 function cuts(L){const masses=L.slice(1).map((x,i)=>P[x]-P[L[i]]);
  for(let i=0;i<masses.length;i++){
   const key=masses[i]+'|'+masses.filter((_,j)=>j!==i).sort((x,y)=>x-y).join(',');
   let row=M[key]??(M[key]=Array(n).fill(0));
   for(let t=L[i];t<L[i+1];t++)row[t]++;
  }
 }
 cuts([0,n]);for(let i=1;i<n;i++){cuts([0,i,n]);for(let j=i+1;j<n;j++)cuts([0,i,j,n]);}
 return rk(Object.values(M),n);
}
let checked=0,pal=0;for(let n=2;n<=8;n++)for(let x=0;x<3**n;x++){let z=x,v=[];for(let i=0;i<n;i++){v.push(3+z%3);z=z/3|0;}let b=v.every((x,i)=>x===v[n-1-i]),r=contract(v);
 if(r!==(b?Math.ceil(n/2):n))throw Error(JSON.stringify({v,r,b}));checked++;if(b)pal++;
}
console.log(JSON.stringify({checked,palindromic:pal}));
{ let seed=246813579,checked=0,nonpal=0;for(let x=0;x<1000;x++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;const n=2+((seed>>>12)%15),M=2*n+11,v=[];for(let j=0;j<n;j++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;v.push(1+M*((seed>>>16)%31));}
const isPal=v.every((x,i)=>x===v[n-1-i]),r=contract(v);if(r!==(isPal?Math.ceil(n/2):n))throw Error(JSON.stringify({v,r}));checked++;nonpal+=!isPal;
}console.log(JSON.stringify({congruentWords:checked,nonpal})); }})();
(()=>{const D=2;
const mul=(a,b)=>[1,a[1]+b[1],a[2]+b[2]+a[1]*b[1]],inv=a=>[1,-a[1],a[1]**2-a[2]];
function desc(v,A){
 const N=v.length,P=[0],Z=[[1,0,0]],O={};for(let i=0;i<N;i++){P.push(P[i]+v[i]);Z.push(mul(Z[i],A[i]));}
 function row(L){const sizes=L.slice(1).map((x,i)=>P[x]-P[L[i]]), C=L.slice(1).map((x,i)=>mul(Z[x],inv(Z[L[i]])));
  const rec=(c,marks)=>{const kk=sizes.map((m,j)=>m+":"+c[j]).sort().join("|");let w=1;for(let i=0;i<c.length;i++)w*=C[i][c[i]];O[kk]=(O[kk]??0)+w;};
  for(let i=0;i<C.length;i++)for(let k=1;k<=D;k++){const c=Array(C.length).fill(0);c[i]=k;rec(c);for(let j=i+1;j<C.length;j++)for(let l=1;l<=D;l++){c[j]=l;rec(c);c[j]=0;}}
 }
 row([0,N]);for(let i=1;i<N;i++){row([0,i,N]);for(let j=i+1;j<N;j++)row([0,i,j,N]);}
 return JSON.stringify(Object.entries(O).sort());
}
let seed=54;const rnd=m=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%m};
let ntry=0,ls=0;
for(let run=0;run<100;run++){
 const n=2+run%7,v=Array(n).fill(0),A=Array.from({length:n},()=>[1,rnd(5)-2,rnd(7)-3]);for(let i=0;i<(n+1)>>1;i++)v[i]=v[n-1-i]=3+rnd(3);
 const P=[[1,0,0]],Q=[[1,0,0]];for(let i=0;i<n;i++){P.push(mul(P.at(-1),A[i]));Q.push(mul(Q.at(-1),A[n-1-i]));}
 const target=desc(v,A);
 for(let m=0;m<2**(n>>1);m++){
 const X=P.map((a,i)=>i>0&&i<n&&((m>>(Math.min(i,n-i)-1))&1)?Q[i]:a);
 const B=X.slice(1).map((x,i)=>mul(x,inv(X[i])));if(desc(v,B)===target){ls++;if(JSON.stringify(B)!==JSON.stringify(A)&&JSON.stringify(B)!==JSON.stringify(A.slice().reverse()))throw Error(JSON.stringify([v,A,B]));}ntry++;
 }
}
console.log(JSON.stringify({flipTests:ntry,valid:ls}));})();

(()=>{function fixture(L){
const v=[6,12,6,6,6], E=[[0,1],[1,2],[2,3],[3,4]];let n=5;
for(let i=0;i<5;i++){let b=v[i]-1-L[i],a=L[i]-b;for(let j=0;j<a;j++)E.push([i,n++]);for(let j=0;j<b;j++){const k=n++;E.push([i,k],[k,n++]);}}
const small=new Map();let goal=0;
function run(mask,disabled){
 const par=Array.from({length:n},(_,i)=>i);
 const rt=i=>{while(i!==par[i])i=par[i];return i;};
 E.forEach(([a,b],i)=>{if((i<4?((mask>>i)&1):disabled.includes(i)))return;par[rt(a)]=rt(b);});
 const h=new Map;for(let i=0;i<n;i++){let j=rt(i);h.set(j,1+(h.get(j)||0));}
 const p=[...h.values()].sort((a,b)=>a-b), key=p.join(",");
 if(key==="1,2,15,18")goal++;
 if(p.reduce((s,x)=>s+(x<=2?x:0),0)<=2)small.set(key,(small.get(key)||0)+1);
}
for(let z=0;z<16;z++){run(z,[]);for(let i=4;i<E.length;i++){run(z,[i]);for(let j=i+1;j<E.length;j++)run(z,[i,j]);}}
return [JSON.stringify([...small].sort()),goal,small.size];
}
const left=fixture([3,7,4,3,4]),right=fixture([4,7,3,4,3]);
if(left[0]!==right[0]||left[1]!==94||right[1]!==95)throw Error(JSON.stringify([left[1],right[1]]));
console.log(JSON.stringify({sameLowMonomials:left[2],first:left[1],second:right[1]}));})();
