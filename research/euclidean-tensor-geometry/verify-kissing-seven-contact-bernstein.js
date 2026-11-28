'use strict';
const fs=require('node:fs'),zlib=require('node:zlib');
const N=Number(process.argv[2]),pp=N*(N-1)/2;
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){[a,b]=[b,a%b];}return a}
function lcm(a,b){return a/gcd(a,b)*b}
function R(a,b=1n){a=BigInt(a);b=BigInt(b);let g=gcd(a,b);return[a/g,b/g]}
function add(a,b){return R(a[0]*b[1]+a[1]*b[0],a[1]*b[1])}
function mul(a,b){return R(a[0]*b[0],a[1]*b[1])}
function pow(a,n){return R(a[0]**BigInt(n),a[1]**BigInt(n))}
function ch(n,k){if(k<0||k>n)return 0n;let a=1n;for(let j=1;j<=k;j++)a=a*BigInt(n-j+1)/BigInt(j);return a}
function floor(a,b){const v=a/b;return a<0n&&a%b?v-1n:v}
function trans(d,lo,hi){
 const h=add(hi,[-lo[0],lo[1]]),A=[];let D=1n;
 for(let i=0;i<=d;i++){let row=[];for(let j=0;j<=d;j++){
  let a=R(0);for(let k=0;k<=Math.min(i,j);k++)a=add(a,mul(mul(pow(lo,j-k),pow(h,k)),R(ch(j,k)*ch(i,k),ch(d,k))));
  D=lcm(D,a[1]);row.push(a);
 }A.push(row);}
 return [A.map(row=>row.map(([a,b])=>a*(D/b))),D];
}
const memo=new Map();
function matrix(d,lo,hi){let k=JSON.stringify([d,lo.map(String),hi.map(String)]);if(!memo.has(k))memo.set(k,trans(d,lo,hi));return memo.get(k)}
function bern(terms,den,ds,lim,up){
 const st=[1,ds[0]+1,(ds[0]+1)*(ds[1]+1)],L=st[2]*(ds[2]+1);
 let V=Array(L).fill(0n);
 for(const[i,j,k,a]of terms)V[i+j*st[1]+k*st[2]]+=BigInt(a);
 for(let ax=0;ax<3;ax++){const dd=ds[ax],s=st[ax],[T,D]=matrix(dd,lim[ax][0],lim[ax][1]),W=Array(L).fill(0n);
  for(let h=0;h<L;h+=s*(dd+1))for(let b=0;b<s;b++){let base=h+b;
   for(let j=0;j<=dd;j++){const v=V[base+j*s];if(v===0n)continue;
    for(let i=0;i<=dd;i++)if(T[i][j])W[base+i*s]+=v*T[i][j];}}
  V=W;den*=D;
 }
 const A=Float64Array.from(V,v=>{const t=v*(1n<<BigInt(N<=130?15:11)),c=up?-floor(-t,den):floor(t,den);if(c>2n**50n||c< -(2n**50n))throw Error('out-of-range normalized Bernstein datum '+c);return Number(c)});
 return {A,ds,stride:st,L}
}
function split(V,k,up){const {A,ds,stride,L}=V,s=stride[k],d=ds[k],W=new Float64Array(L),Zz=new Float64Array(L),u=new Float64Array(d+1);
 for(let h=0;h<L;h+=s*(d+1))for(let b=0;b<s;b++){const base=h+b;for(let j=0;j<=d;j++)u[j]=A[base+j*s];W[base]=u[0];Zz[base+d*s]=u[d];for(let j=1;j<=d;j++){
  for(let i=0;i<=d-j;i++){const t=(u[i]+u[i+1])/2;u[i]=up?Math.ceil(t):Math.floor(t);}W[base+j*s]=u[0];Zz[base+(d-j)*s]=u[d-j];}}
 return [{...V,A:W},{...V,A:Zz}];
}
function check(V,G,mask){const dim=V.ds.length;let nodes=0,close=0,out=0;
 function go(U,Q,lo,hi,d){
  nodes++;if(nodes>3000000||d>72)throw Error('unresolved Bernstein box');
  if(lo.some((v,i)=>i<dim-1&&mask[i]&&v>hi[i+1])){out++;return;}
  if(U.A.every(x=>x>=0)){close++;return;}
  if(Q){
   if(Q.A.every(v=>v<0)){out++;return;}
   if(Q.A.every(v=>v>=0))Q=null;
   else{
    let lb=0,ub=Infinity;const ua=U.A,qa=Q.A;for(let i=0;i<ua.length;i++){let x=ua[i],y=qa[i];if(y>0)ub=Math.min(ub,x/y);else if(y<0)lb=Math.max(lb,x/y);else if(x<0){ub=-1;break;}if(lb>ub)break;}
    if(lb>0&&ub>=lb){
     const p=2**(Math.floor(Math.log2(lb))-16),a=Math.ceil(lb/p);if(a*p<=ub&&Number.isSafeInteger(a)&&qa.every((v,i)=>Number.isSafeInteger(v*a)&&ua[i]>=(v*a)*p)){close++;return;}
    }
   }
  }
  const k=d%dim,[l,r]=split(U,k,false),[p,q]=Q?split(Q,k,true):[null,null],mid=(lo[k]+hi[k])/2,h=hi.slice(),a=lo.slice();h[k]=mid;a[k]=mid;go(l,p,lo,h,d+1);go(r,q,a,hi,d+1);
 }
 go(V,G,Array(dim).fill(0),Array(dim).fill(1),0);return {nodes,close,out};
}

const gram=[[0,0,0,1],[1,1,1,2],[2,0,0,-1],[0,2,0,-1],[0,0,2,-1]];
let text=fs.readFileSync(0,'utf8').trim().split(/\s+/).at(-1);
const[unit,terms]=JSON.parse(zlib.inflateSync(Buffer.from(text,'base64'))),D=BigInt(unit),ds=[0,0,0];
for(const e of terms)for(let i=0;i<3;i++)ds[i]=Math.max(ds[i],e[i]);
if(ds.some(d=>d>35||d<2))throw Error('unexpected degree');
const nn=process.argv.slice(3).map(Number),th=R(nn[0],nn[1]),claim=nn[2],low=[R(-1),th],high=[th,R(1,2)];
if(N<127||N>132||nn.slice(3).join(',')!=='0,1,2,3'||!nn.every(Number.isSafeInteger)||nn[1]<=0||nn[2]<1)throw Error('invalid proof parameters');
for(const m of nn.slice(3)){let lim=Array(3-m).fill(low).concat(Array(m).fill(high)),mask=[lim[0]===lim[1],lim[1]===lim[2]];
 const constterm=R(100*m*pp-3*(100*(claim-1)+1),300);
 const den=lcm(D,constterm[1]),T=terms.map(([i,j,k,y])=>[i,j,k,BigInt(y)*(den/D)]);
 T.push([0,0,0,constterm[0]*(den/constterm[1])]);
 const V=bern(T,den,ds,lim,false),G=bern(gram,1n,ds,lim,true),s=check(V,G,mask);console.log('OK STRAT',m,'CLAIM',claim,s.nodes,s.close,s.out);
}
