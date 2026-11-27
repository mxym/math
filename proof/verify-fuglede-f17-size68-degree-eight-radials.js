'use strict';

const P = 17;
const N = P*P;
const mod = x => (x%P+P)%P;
const inv = Array(P).fill(0);
for (let a=1; a<P; ++a)
  for (let b=1; b<P; ++b)
    if (a*b%P===1) inv[a]=b;
const dir = (a,b) => {
  const dx = mod(a%P-b%P);  
  return dx===0 ? P
    : mod((Math.floor(a/P)-Math.floor(b/P))*inv[dx]);
};
const dirs = Array.from({length:N},(_,a)=>
  Uint8Array.from({length:N},(_,b)=>dir(a,b)));
const intercept = (a,s) => s===P ? a%P
    : mod(Math.floor(a/P)-s*(a%P));
const T = [0,1,P];
const forced = (1<<0)|(1<<(P-1))|(1<<P);


const perm=[];
for(let a of T)for(let b of T)for(let c of T)if(a!==b&&a!==c&&b!==c){
 const modv=(s,d)=>[mod(d%P-s%P),mod((d/P|0)-(s/P|0))];
 const [x,y]=modv(a,b),[u,v]=modv(a,c);
 perm.push(Array.from({length:P+1},(_,s)=>{const i=s===P?0:1,j=s===P?1:s;
 const X=mod(x*i+u*j),Y=mod(y*i+v*j);return X?mod(Y*inv[X]):P;}));
}
function masksymm(mask){
 for(const f of perm){let S=0;for(let d=0;d<=P;d++)if(mask&(1<<d))S|=1<<f[d];if(S<mask)return false;}
 return true;
}


function run(k,sz,ctarget){let masks=0,nodes=0,exam=0,max=0,ex=null;const T=[0,1,P],lim=1<<P;
function runMask(mask){if(!masksymm(mask))return;masks++;let compat=Array.from({length:N},(_,a)=>Uint8Array.from({length:N},(_,b)=>+(a===b||!!(mask&(1<<dirs[a][b])))));
let Q=Array.from({length:N},(_,i)=>i).filter(i=>T.every(t=>compat[t][i]));
let cn=new Uint8Array((P+1)*P),C=T.slice();
function upd(a,z){for(let s=0;s<=P;s++)cn[s*P+intercept(a,s)]+=z;}T.forEach(t=>upd(t,1));
function dfs(tail,Q){nodes++;if(Q.length<ctarget||C.length+tail.length<sz)return;if(C.length===sz){exam++;if(Q.length>max){max=Q.length;ex={mask,C:C.slice(),Q};}return;}
for(let i=0;i<tail.length;i++){const a=tail[i];if(C.some(b=>{let s=dirs[a][b];return cn[s*P+intercept(a,s)]>=4;}))continue;
C.push(a);upd(a,1);dfs(tail.slice(i+1).filter(t=>compat[a][t]),Q.filter(t=>compat[a][t]));upd(a,-1);C.pop();
}}
dfs(Q.filter(x=>!T.includes(x)),Q);}
function gen(mask,x,s){if(!s){runMask(mask);return;}for(let t=x;t<P-1;t++)gen(mask|(1<<t),t+1,s-1);}
gen(forced,1,k-3);if(exam||nodes!==(k===6?140:4262))throw Error("dominating full arms");console.log({k,sz,ctarget,masks,nodes,exam});
}
for(let k of [6,7])run(k,6,17);

const Fr=Array.from({length:17},(_,i)=>i);
function allowed(y,a){
 let f=[1];
 for(let r of [7,8,9,10]){let z=Array(f.length+1).fill(0);for(let j=0;j<f.length;j++){z[j]=mod(z[j]+f[j]);z[j+1]=mod(z[j+1]-(a+r)*f[j]);}f=z;}
 const t=[1,0,mod(3*y*y),0,mod(15*y**4)],q=[1];
 for(let i=1;i<=3;i++)q[i]=mod(t[i]-f.slice(1,i+1).reduce((s,x,j)=>s+x*q[i-j-1],0));
 return mod(f[4]+f[3]*q[1]+f[2]*q[2]+f[1]*q[3])===t[4];
}
let pairs=[];
for(let y=2;y<17;y++)for(let a of Fr)if(allowed(y,a)&&allowed(y-1,a))pairs.push([y,a]);
if(String(pairs)!=="6,4,6,13,9,0,9,5,9,12,12,4,12,13")throw Error("single radial support roots");
console.log({pairs});
