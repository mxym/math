'use strict';
const zlib=require('node:zlib');
function gcd(x,y){if(x<0n)x=-x;if(y<0n)y=-y;while(y){let t=x%y;x=y;y=t;}return x;}
function R(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('zero denominator');if(d<0n){n=-n;d=-d;}const z=gcd(n,d);return [n/z,d/z];}
const Z=R(0),O=R(1),add=(x,y)=>R(x[0]*y[1]+x[1]*y[0],x[1]*y[1]),mul=(x,y)=>R(x[0]*y[0],x[1]*y[1]),neg=x=>[-x[0],x[1]],cmp=(x,y)=>x[0]*y[1]-x[1]*y[0], show=x=>x.join('/');
const P=(k=0,c=O)=>c[0]?new Map([[k,c]]):new Map();
function put(A,k,v){if(!v[0])return;const c=add(A.get(k)||Z,v);if(c[0])A.set(k,c);else A.delete(k);}
function plus(A,B){const C=new Map(A);for(const [k,b]of B)put(C,k,b);return C;}
function scale(A,b){const C=P(0,Z);for(const [k,v]of A)put(C,k,mul(v,b));return C;}
function prod(A,B){const C=P(0,Z);for(const[i,a]of A)for(const[j,b]of B)put(C,i+j,mul(a,b));return C;}
const sum=(...A)=>A.reduce(plus,P(0,Z)),diff=(A,B)=>plus(A,scale(B,R(-1))),a=P(1),b=P(32),c=P(1024);
function bases(x,k){const p=[P(),x];for(let j=2;j<=k;j++)p.push(diff(scale(prod(x,p[j-1]),R(2)),p[j-2]));return p;}
function lin(u,p){return sum(...u.map((v,i)=>scale(p[i],v)));}
const enc=(i,j,k)=>i+32*j+1024*k,idx=v=>[v%32,(v>>5)%32,v>>10];
function build(data,ep,et){
 const[n,q,d,D,h,g,B,fac]=data,den=BigInt(D),ch=bases(a,g.length),chb=bases(b,d),ab=prod(a,b),w=diff(c,ab),z=prod(diff(P(),prod(a,a)),diff(P(),prod(b,b))),Q=[P(),w];
 if(h.some(x=>x<0)||fac.length!==d+1)throw Error('not a positive kernel');
 for(let k=1;k<d;k++)Q.push(scale(diff(scale(prod(w,Q[k]),R(2*k+n-3)),scale(prod(z,Q[k-1]),R(k))),R(1,k+n-3)));
 let K=P(0,Z);for(let k=0;k<=d;k++){const M=fac[k];if(M.length!==d+1-k||M.some(r=>r.length!==M[0].length))throw Error('factor dimensions');let S=P(0,Z);
  for(let j=0;j<M[0].length;j++){const u=M.map(r=>R(r[j],den));S=plus(S,prod(lin(u,ch),lin(u,chb)));}K=plus(K,prod(S,Q[k]));}
 let H=P(0,Z);for(const[e,v]of K){const[i,j,k]=idx(e),u=mul(v,R(1,3));for(const ee of [e,enc(j,k,i),enc(k,i,j)])put(H,ee,u);}
 const gp=lin(g.map(x=>R(x,den)),ch);let T=diff(P(0,ep),H);for(const[i,v]of gp)for(const e of [i,i*32,i*1024])put(T,e,v);
 const cc=[P(),a];for(let k=1;k<h.length;k++)cc.push(scale(diff(scale(prod(a,cc[k]),R(2*k+n-2)),scale(cc[k-1],R(k))),R(1,k+n-2)));
 const hp=lin(h.map(x=>R(x,den)),cc.slice(1)),aa=prod(a,a),f=diff(prod(aa,aa),scale(aa,R(1,4)));let H11=P(0,Z),H111=Z;
 for(const[e,v]of H){const[i,j,k]=idx(e);put(H11,j+k,v);H111=add(H111,v);}
 const Y=diff(P(0,add(R(B,den),et)),sum(f,hp,scale(H11,R(3)),scale(gp,R(3*(q-2)))));
 const energy=[R(3,4),R(h.reduce((v,w)=>v+BigInt(w),0n),den),H111,mul(R(q-1),add(R(B,den),et)),mul(R((q-1)*(q-2)),ep)].reduce(add,Z);
 return [T,Y,energy];
}
function choose(n,k){if(k<0||k>n)return 0n;let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-i+1)/BigInt(i);return x;}
function divfloor(x,d){let z=x/d;return x<0n&&x%d?z-1n:z;}
function bern(A,dim,up=false){
 const ds=Array(dim).fill(0);for(const i of A.keys())idx(i).slice(0,dim).forEach((v,j)=>ds[j]=Math.max(ds[j],v));const stride=ds.map((_,j)=>ds.slice(0,j).reduce((s,n)=>s*(n+1),1)),L=ds.reduce((s,n)=>s*(n+1),1),v=Array(L).fill(Z);
 for(const[i,r]of A){const I=idx(i);if(I.slice(dim).some(x=>x))throw Error('nonunivariate');v[I.slice(0,dim).reduce((s,n,k)=>s+n*stride[k],0)]=r;}
 let V=v;
 for(let k=0;k<dim;k++){const d=ds[k],s=stride[k],W=V.slice(),T=Array.from({length:d+1},(_,i)=>Array.from({length:d+1},(_,j)=>{let f=Z;for(let t=0;t<=Math.min(i,j);t++)f=add(f,R(choose(j,t)*choose(i,t)*BigInt((j-t)%2?-1:1)*3n**BigInt(t),choose(d,t)*2n**BigInt(t)));return f;}));
  for(let i=0;i<L;i++){const t=Math.floor(i/s)%(d+1),base=i-t*s;let x=Z;for(let j=0;j<=d;j++)if(V[base+j*s][0]&&T[t][j][0])x=add(x,mul(T[t][j],V[base+j*s]));W[i]=x;}V=W;
 }
 const gg=Float64Array.from(V,r=>{const n=r[0]*(1n<<42n),v=up?-divfloor(-n,r[1]):divfloor(n,r[1]);if(v>2n**50n||v< -(2n**50n))throw Error('dyadic guard');return Number(v);});return {A:gg,ds,stride,L};
}
function split(V,k,up){const {A,ds,stride,L}=V,s=stride[k],d=ds[k],W=new Float64Array(L),Zz=new Float64Array(L),u=new Float64Array(d+1);
 for(let h=0;h<L;h+=s*(d+1))for(let b=0;b<s;b++){const base=h+b;for(let j=0;j<=d;j++)u[j]=A[base+j*s];W[base]=u[0];Zz[base+d*s]=u[d];for(let j=1;j<=d;j++){
  for(let i=0;i<=d-j;i++){const t=(u[i]+u[i+1])/2;u[i]=up?Math.ceil(t):Math.floor(t);}W[base+j*s]=u[0];Zz[base+(d-j)*s]=u[d-j];}}
 return [{...V,A:W},{...V,A:Zz}];
}
function check(V,G){const dim=V.ds.length;let nodes=0,close=0,out=0;
 function go(U,Q,lo,hi,d){nodes++;if(nodes>9000000||d>75)throw Error('unresolved Bernstein box');if(U.A.every(x=>x>=0)){close++;return;}if(Q&&(Q.A.every(x=>x<0)||lo.some((v,i)=>i<dim-1&&v>hi[i+1]))){out++;return;}
  const k=d%dim,[l,r]=split(U,k,false),[p,q]=Q?split(Q,k,true):[null,null],mid=(lo[k]+hi[k])/2,h=hi.slice(),a=lo.slice();h[k]=mid;a[k]=mid;go(l,p,lo,h,d+1);go(r,q,a,hi,d+1);}
 go(V,G,Array(dim).fill(0),Array(dim).fill(1),0);return {nodes,close,out};
}
const determinant=sum(P(),scale(prod(prod(a,b),c),R(2)),scale(sum(prod(a,a),prod(b,b),prod(c,c)),R(-1)));

const charts = [
'eJxtUtmtxEAIayUFJBL3UUu0/bfxDJPPF+0qEwawsXnjvrjvy/Gi77mvF///fz9cPuzWxHJfjzh5B80pmIQLJzbT6IkxqZWj+6Nu2T4haZe5MxGOCXjnfGul4ZVDZlAeZVf1IfO+VkgFwkC6u3xkB63UmCIXjYNS4nf464SylxBKDKfsqNqQBbl02Y4jgkagzLiINNAU85L55PLABENUBNWs2354cMdCqAnQRaKXWDJ3aq42EgRCU6BbIaUAV2inMwErLyRltU1CthknH43vq6EfnAkbCZ1MBQpJFU4zuRlhnP5N+st6BCcLnyKhtgWLnoEeqSQVrWUPCzaWaaiKYJ0aiVJuXZ1Ioe7mcs5qaHWdoWIitgjUa6kJCagdLR0G2toK1XCrHoKObHCTEx14RORN1hZdalgcibU8I3w20jGPrgEQ0Ei/KR8PXaUAF6RrbiC58mhGMa6JQrGV1rAzlbyTzKb48FWzpFmzR0gzeh31iBwKiV1KP5vqrdR5kK17yIux5XGI7bgJG88WJc8GY5nM6eMbHNZzgnjFTieq5Q4Tf3j+ACDFsm8=',
'eJxtUtut5FAIayUFJBLvRy3R9N/GNZzs30YzCgEDxvDmfXHfl+NF33NfL/7///0QfDhYqpHySHQnr5Uc5aj2sLtJ01hUTlawtFxjg5opY5gjNI7UGqwxMV5pdro8wHdToN/7bsxMx60BH6qo4KuIv3pMISZUv8Oep+ZCNNETRnIWyE6rVO3Q3FmGXkiMW6ZbNffhVR7EQ16MhLz+lUZIxo3ZoJs5KXgVpWbxSkKWVTHoWmINfTndEEVjHac3K/noVlrScbgAkBbgKm0zg3C7zVdoJR3RUth+g34x2X2hTuqwdwyE4mAE7CoqFerOfUpzGGBOvaons7csSCD5rCYq3MwX3Wd9AuFGGkns2AZuhTXvvk0JwrIMHiBBQkbMjOjltVtnK5UYDdGe4oCfHqy4qhuEUSPTUWjuJly+u4GCGt+cYhB/uDp650JVTY7ED7JGI8znRyOlybcNqsfuSh28aTlFlBgv7bA5jAeeFj4TO4gxf40jso4XZ8abwyQ7Gm5d1qFoO4qKtkHKk6nhubrjRpLUj9dwumX0w/MHGsuw1w=='
];
for(const [i,chart] of charts.entries()){
 const M=JSON.parse(zlib.inflateSync(Buffer.from(chart,'base64')).toString('utf8')),n=6+i,q=19;
 if(M[0]!==n||M[1]!==q||M[2]!==5||M[3]!==100000000)throw Error('wrong chart');
 const [T,Y,U]=build(M,R(1,40000),R(1,200000));
 const pair=check(bern(Y,1),null),triple=check(bern(T,3),bern(determinant,3,true));
 const exact=i?R(1577227253193267n,1000000000000000n):R(3154135879149453n,2000000000000000n);
 if(cmp(U,exact)!==0n||cmp(U,R(19,12))>=0n)throw Error('energy bound');
 // Normalize difference axes of the marked pairs. Test the actual rational margin.
 const p=i?54:27,s=9,h=i?R(1,12000):R(1,6000),h2=mul(h,h),div=(x,y)=>R(x[0]*y[1],x[1]*y[0]),sq=x=>mul(x,x),oneMinus=add(O,neg(h2));
 const A=sq(div(add(R(1,2),h2),oneMinus)),C=div(sq(add(R(1,2),h)),oneMinus),phi=x=>mul(x,add(x,R(-1,4)));
 const margin=[R(3*s,4),mul(R(-s*s,q),U),mul(R(-p*(p-1)),phi(A)),mul(R(-2*p*s),phi(C))].reduce(add,Z);
 if(cmp(margin,Z)<=0n)throw Error('near-pair bound '+show(margin));
 console.log({n,q,energy:show(U),pair,triple,halfChord:show(h),margin:show(margin)});
}
