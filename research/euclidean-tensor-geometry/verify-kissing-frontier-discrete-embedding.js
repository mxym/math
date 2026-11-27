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


const pow=(x,k)=>R(x[0]**BigInt(k),x[1]**BigInt(k)),sub=(a,b)=>add(a,neg(b)),le=(a,b)=>cmp(a,b)<=0n,gt=(a,b)=>cmp(a,b)>0n,sm=(a,b)=>le(a,b)?a:b,lg=(a,b)=>le(a,b)?b:a;
function isqrt(x){if(x<0n)throw Error('sqrt domain');if(x<2n)return x;let y=1n<<BigInt(Math.ceil(x.toString(2).length/2));while(true){let z=(y+x/y)>>1n;if(z>=y)return y;y=z;}}
const scaleRoot=1000000n,loS=x=>R(isqrt(x[0]*scaleRoot*scaleRoot/x[1]),scaleRoot),hiS=x=>add(loS(x),R(1,scaleRoot));
const m=[0,1,3,6,12,20,36,63];
function imm(d,seen,num){let t=O;if(seen+num>m.length)throw Error('flat range');for(let j=0;j<num;j++)t=mul(t,R(Math.max(0,d-m[seen+j]),j+1));return t;}
function rowlow(p,r){let d=p-r,I=[O];for(let j=1;j<=Math.min(m.length,r);j++)I.push(imm(d,0,j));let L=I.reduce(add,Z);let x3=choose(d,2)/3n,x4=(5n*choose(d,3)+BigInt(Math.max(0,d-8))*x3)/4n;for(const[j,x]of[[1,0n],[2,0n],[3,x3],[4,x4]])if(j<I.length)L=add(L,lg(Z,sub(I[j],R(x))));return L;}
function collow(p,h,r,theta){const t=r-h,da=p-h,b=21-t;if(t<0||b<0)throw Error('rank range');let L=Z,u=O;for(let k=0;k<=3&&k<=r;k++){if(k)u=mul(u,R(Math.max(0,b-(3**(k-1)-1)),k));let w=Z;for(let j=0;j<=Math.min(m.length-k,r-k);j++)w=add(w,imm(da,k,j));L=add(L,mul(mul(u,pow(theta,t+k)),w));}return L;}
function productCheck(n,r,D,S,lower2){
 // Split the squared error budget: x goes to the largest n singular values.
 const steps=512,t=r-n;if(t<=0)throw Error('rank not excess');let upper=Z;
 for(let i=0;i<steps;i++){
  const x=mul(D,R(i+1,steps)),remaining=mul(D,R(steps-i,steps*t));
  const head=mul(add(S,hiS(mul(R(n),x))),R(1,n));
  upper=lg(upper,mul(pow(head,2*n),pow(remaining,t)));
 }
 if(!gt(lower2,upper))throw Error('product rank '+[n,r,Number(lower2[0])/Number(lower2[1]),Number(upper[0])/Number(upper[1])]);
}
const gamma=R(10,21),theta=R(20,21);
for(const[n,p,bytes,ep,et,U0,Dstar,B,markedMax,totalMax,dist]of [
 [6,26,'eJxdVYuNKzkMayUFJID1tVRL8Ppv45GcHA53i90dx/FIFEnJ336/3N6veb/s/H7er6/HvVPvF9YT0bNa5r11rpa/3z84+6mK8ny/Pp7nJAJ+5vod7uxEO55xIgtpzKcRNr0Sj/E2HK9JJvBra3znMMfHb9vR81TweZyIPmZnuZ9nl6miACKyzRKfv9+vTzKltQ+P3RQSS2tGBwBk18LtsuydGi4Q2XvCU0W5cFcKw2wZMNTaxeMO3uF2TKyODcqxYuU9fpKIviEU3r3armWu6OM6VsWU5WAK3w8C38uDdjzslAlDHCKuE8QLkIWIfkIkGepHhCkUQSwFCHVWMt7NeqrIOK0ykhTm4giTBECClEQyfr42TQHv7TEJ0w3Spa6fgho3hCFiDgJZJc4xEHiR4IA8Z4zwboIUnMl0qDyMAd5Caai29b18t1Co0wpuVD/3aB+EQ2cszK4h1DxMZEnTIptRRtIgcHE38jTRzcI5oMQ9Day8X303vBSg5b3TlPlG9YP5DsWAdw4T7lzRZAc8kZ44iQP9hwG+7rLPzVpn7km5ySOv7JlmI2NBWDhPCeCm44QKF+4FXjGaJUMjOSP1hjRJ26S/1/tsiYe1xTkPOKlj1RneF05hFNJIxaAhU/EUIHs2KFJPMxD5xatylscU5JUbtxqSPyZb96d5rTPraRzZYnay1BcAauxegOxodp+dAXuis85cdH1I6Mecc4wMB75ohe6aoSLAsKvuRReni/4P3+6jfjqFg9kMhfjYwui57EDPuiR8gUnvR9VeNuMH/QwPERMqdjIGwGkgzR9IvZpEe11MQdRUU6CJVy6G3S7J+zTEdPo5cSKlG/wDfynQ2GiU9QnOsApoSn2Ob6lskiMnguuo6aBVYZeR9xA5HiuheDqewtDmam9DT6XMC+sGZw2GKfpSiAMtcjRUPmwxoz2a3N1t9iOK68OW4fQaxkZjwvsjUe7I5KlZTmtUBx3hmsIpoeun9EUp56zqFSPHTDU3k3KANDcSrk2ijAu8mi2WbNt4QM4VHVfzyK5CYbo+wyjhDjUTaqr4DSTIBM0eY2t6BOlDPTJswOyahegx2JSJYzc1RxITqnefoS0ms3/T/M7DX7UQID3G81XHb2jkZ6BZfX+6gHwyDx0FygtJR60BKZ5LCGMeAP7JdmgSn2ccBYbNymLQbeZZgeB9bhSHMM8cn76qUPcZ7tbqx5mLL2rlfji5deHSl7dgbTIaGF3Bqf/ZpsEeS3TqYvg0uky8YyhQLdyH/Vw2Bx6sZ5qjNdQN0FWdiUtXRseFxI7SvQgd+0cJ//3n7yEKl5kaGxdJ4CaQbBTksb4FWH7GNihizRe7E88enCNyQVKd8780/356Vvj5C343tFA=',750000,100000,'9505462750363939/6000000000000000',R(47,50),R(1094,100),11,11,1],
 [7,53,'eJxtVIlx5DAMa2ULWM3wf2rxXP9tHEgll2Ry3seyLJIgAOnJ90v4/cKN6eN6vx6mrMQcxi4SzTv88f2DZSIa7Rryfpmai6ojSBs3rXYM1YsytVElwoMlMeRGdrbJyhrkUoUMFQjMLpQkIZOpL2Hq1qjHYkrEiHamklBMZYY6klhbqb1f3ayzlJIGHld0EN4/z3O4BplP0sMcGkikqXh0S4DEtDJrJu0CDbeK6RHPWkjunjKLqokwiKBITCNVGRqbKAIHIT1RvREGuCeqUay9Sac1oB4MWBc8ZBwBwwSWJuxMHiMCCQnqUMZks3gLy7RW4IsmgZJUSt2oycNQAhFssWWrq2KnpYR9RqrEd47wVlk/S4LcXqhBwz+Tcw0yMBk94jKx1lKnAPRZ1Vc/w3y1BhJfXUBfVm2cmdMWhB8k/IPPX1aa+ce2ZhjbNpoeiVCF7jIiA00XgE060Fwsm060RwYAEy/0UA4zzLO5i008/GmDyo0MUizPbFe7lKlxYDyZxUfaYKYdBbtJTaBaVdYa/liJj5nJ1iigZ5Q+rk2jEhw5dByBMgqqFuGuKDh/XD6vaCEyWehKhTu38mwXdt0g5eENbDcvePag3WcM6L1iqcKL06pZgn/7H7mXWdA/ahwObFhYkdaBiRZvAkXKhN+XmS02WBpGQqeOjxYvSyCbawuB/ekq19sWLndftSTxrB3ys2P3As/hwhJbiirJ1/97Kow94ay4VrSBZw6rQEjgu1pjJW/6xHEDZ/1q9HapPbCZcApkbwnsFHhoNajRmXE+CNs9GTztSgq/rdGSi2nrp7RvmEru0RNQz3b3KWGvfwNwS8/fv9/Pma+nO8L1F4onFew=',150000,400000,'23807257697230457/15000000000000000',R(31,25),R(11036,1000),13,12,6]]){
 const C=JSON.parse(zlib.inflateSync(Buffer.from(bytes,'base64')));if(C[0]!==n||C[1]!==21)throw Error('chart');const[T,Y,U]=build(C,R(1,ep),R(1,et)),pair=check(bern(Y,1)),triple=check(bern(T,3),bern(determinant,3,true));if(show(U)!==U0)throw Error('energy');
 const delta=sub(mul(R(100,21),U),R(15,2)),D=mul(R(64,3),delta),c=sub(R(6,n+4),R(1,4)),mu=R(p+10,n);if(!gt(Dstar,D))throw Error('D');
 const part=k=>k===0?Z:k<=n?R(k+1,2):mul(add(R(k),hiS(R((k-2)**2+8*n))),R(1,4));
 for(let k=0;k<=21;k++)if(!gt(B,add(part(k),part(21-k))))throw Error('hemisphere bounds');
 const m0=sub(mu,mul(gamma,B));if(!gt(m0,Z)||!gt(pow(mul(R(2),m0),2),mul(delta,add(mul(R(4),R(c[1],c[0])),R(64,3)))))throw Error('positive inertia');
 const den=4096;for(let j=0;j<den;j++){const lo=R(j,den),hi=R(j+1,den),rem=sub(delta,mul(c,pow(lo,2)));if(rem[0]<0n)break;
  const s=sub(m0,hi);if(s[0]<=0n||!gt(mul(R(2),loS(s)),add(hiS(R(dist-1)),hiS(mul(R(64*21,3*10),rem)))))throw Error('label separation '+[n,j]);
 }if(!gt(c,delta))throw Error('e bound');
 if(n===6){const L=rowlow(p,12);productCheck(n,12,Dstar,R(2*p),pow(L,2));}
 const S=mul(R(2),hiS(mul(R(p),add(R(p),mul(R(21),theta)))));
 for(let r=totalMax+1;r<=Math.min(p,markedMax+21);r++){
  let L=null;for(let h=n;h<=Math.min(r,markedMax);h++)if(r-h<=21){let z=collow(p,h,r,theta);L=L===null?z:sm(L,z);}
  if(L===null)continue;productCheck(n,r,Dstar,S,mul(rowlow(p,r),L));
 }
 console.log(JSON.stringify({n,p,energy:show(U),delta:show(delta),D:show(D),squaredDistanceAtLeast:dist,totalRankAtMost:totalMax,pair:pair.nodes,triple:triple.nodes}));
}
