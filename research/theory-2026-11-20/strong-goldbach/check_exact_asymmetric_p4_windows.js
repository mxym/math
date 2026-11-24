// Directed BigInt endpoint enclosures for the two P4 window margins.
// Run with Node.js. All scales and cutoffs are exact integers.
function replay() {
const M=20000n,S=10n**15n,U=1000000n,unit=10n**10n,step=5n;
const D=241590n,mu=39300n,beta=313500n,T=214300n,eps=10n;
const ceil=(x,y)=>(x+y-1n)/y;
const end=Number(D*M/mu);
let gl=Array(end+1).fill(0n),gu=gl.slice(),hl=gl.map(()=>S),hu=hl.slice();
const n=Number(M);
for(let i=2*n+1;i<=end;i++){
 const lo=BigInt(i-n),hi=lo-1n;
 gl[i]=gl[i-1]+hl[i-n-1]/lo;
 gu[i]=gu[i-1]+ceil(hu[i-n],hi);
 if(i>3*n){hl[i]=hl[i-1]+gl[i-n-1]/lo;hu[i]=hu[i-1]+ceil(gu[i-n],hi);}
}
let c1=0n;for(let a=mu;a<T;a+=step){
 let b=a+step,j=Number(ceil((D-a)*M,mu));j=Math.max(2*n,j);
 c1+=ceil(step*(beta-a)*U*hu[j]*unit,beta*a*(D-b)*S);
}
const jl=[],ju=[];let rl=S/2n,ru=S/2n;
for(let i=0;i<=4*n;i++){
 const r=BigInt(i),l=r-1n;
 if(i>n){rl-=ceil(ju[i-n]*M*M,l*l*l);ru-=jl[i-n-1]*M*M/(r*r*r);}
 jl[i]=rl*r*r/(M*M);ju[i]=ceil(ru*r*r,M*M);
}
const rows=[];
for(const [theta,rho] of [[483200n,483200n],[500000n,491600n]]){
 let c2=0n;
 for(let a=T;a<beta;a+=step){
  const b=a+step,p=rho-b-2n*eps,q=2n*mu;
  const J=jl[Number(p*M/q)];
  if(J<=0n)throw Error("J interval");
  c2+=ceil(step*(beta-a)*theta*U*S*unit,beta*a*2n*mu*mu*J);
 }
 const etan=5n*beta-U,etad=beta;
 const cert=gl[end]*U*unit*etan-(c1+c2)*etad*S*D;
 const denom=S*D*unit*etan;
 if(cert*200n<=denom)throw Error("margin at most 0.005");
 rows.push({theta:String(theta),rho:String(rho),c2:String(c2),marginFloor10000:String(cert*10000n/denom)});
}
return {end,g:String(gl[end]),c1:String(c1),rows};
}
console.log(JSON.stringify(replay(), null, 2));
