// Exact field checks for localization symmetries and the two-localization kernel.
const mod=(x,p)=>((x%p)+p)%p;
function pow(a,k,p){let y=1;for(;k;k>>=1,a=mod(a*a,p))if(k&1)y=mod(y*a,p);return y;}
const f=(a,b,x,p)=>mod(a*x+b,p);
const mob=(a,b,c,d,x,p)=>{
 if(!mod(c*x+d,p)) throw Error("unexpected pole");
 return mod(f(a,b,x,p)*pow(mod(c*x+d,p),p-2,p),p);
};
const prime=p=>p>=2&&!Array.from({length:Math.floor(Math.sqrt(p))-1},(_,i)=>i+2).some(d=>p%d===0);
let primes=0,triples=0,checks=0,kernel=0;
for(let p=5;p<=257;p+=4)if(prime(p)){
 primes++;
 const chi=x=>mod(x,p)?pow(mod(x,p),(p-1)/2,p)===1?1:-1:0;
 const F=Array.from({length:p},(_,i)=>i),S=F.filter(x=>chi(x)===1&&chi(x-1)===1);
 if(S.length!==(p-5)/4)throw Error("wrong size");
 function auto(T,F){
  const U=T.map(F),Uset=new Set(U);
  if(Uset.size!==T.length||U.some(x=>!T.includes(x)))throw Error("not a permutation");
  for(let i=0;i<T.length;i++)for(let j=0;j<i;j++){
   if(chi(T[i]-T[j])!==chi(U[i]-U[j]))throw Error("not a graph automorphism");checks++;
  }
  return T.filter((x,i)=>x===U[i]);
 }
 const r=auto(S,x=>mob(-1,1,0,1,x,p)),s=auto(S,x=>mob(0,1,1,0,x,p)),z=auto(S,x=>mob(0,1,-1,1,x,p));
 const e=chi(2)===1?1:0,h=p%3===1?1:0;
 if(r.length!==e||s.length!==e||z.length!==2*h)throw Error("S3 character");
 const H=F.filter(v=>chi(v)===1&&v!==1&&v!==p-1),x=z=>mod((z+2+pow(z,p-2,p))*pow(4,p-2,p),p);
 const xH=H.map(x);
 if(H.length!==2*S.length||S.some(v=>xH.filter(y=>y===v).length!==2))throw Error("bad parametrization");
 for(const v of H)for(const w of H){
  if(chi(x(v)-x(w))!==chi(1-w*pow(v,p-2,p))*chi(1-v*w))throw Error("kernel factorization");kernel++;
 }
 if(p>101)continue;
 for(const t of S){
  triples++;
  const T=S.filter(x=>chi(x-t)===1),K=[auto(T,x=>mob(0,t,1,0,x,p)),auto(T,x=>mob(1,-t,1,-1,x,p)),auto(T,x=>mob(t,-t,1,-t,x,p))];
  if(K.some(A=>A.length!==0&&A.length!==2)||K.some((A,i)=>K.some((B,j)=>i!==j&&A.some(v=>B.includes(v)))))throw Error("V4 character");
 }
}
console.log(JSON.stringify({primes,triples,checks,kernel}));
