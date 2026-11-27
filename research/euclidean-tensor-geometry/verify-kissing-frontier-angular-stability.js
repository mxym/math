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


const pow=(x,k)=>R(x[0]**BigInt(k),x[1]**BigInt(k));const lt=(a,b)=>cmp(a,b)<0n;
const charts=[
 [6,26,750000,100000,'9505462750363939/6000000000000000',47,50,238,100,12,1,3,'eJxdVYuNKzkMayUFJID1tVRL8Ppv45GcHA53i90dx/FIFEnJ336/3N6veb/s/H7er6/HvVPvF9YT0bNa5r11rpa/3z84+6mK8ny/Pp7nJAJ+5vod7uxEO55xIgtpzKcRNr0Sj/E2HK9JJvBra3znMMfHb9vR81TweZyIPmZnuZ9nl6miACKyzRKfv9+vTzKltQ+P3RQSS2tGBwBk18LtsuydGi4Q2XvCU0W5cFcKw2wZMNTaxeMO3uF2TKyODcqxYuU9fpKIviEU3r3armWu6OM6VsWU5WAK3w8C38uDdjzslAlDHCKuE8QLkIWIfkIkGepHhCkUQSwFCHVWMt7NeqrIOK0ykhTm4giTBECClEQyfr42TQHv7TEJ0w3Spa6fgho3hCFiDgJZJc4xEHiR4IA8Z4zwboIUnMl0qDyMAd5Caai29b18t1Co0wpuVD/3aB+EQ2cszK4h1DxMZEnTIptRRtIgcHE38jTRzcI5oMQ9Day8X303vBSg5b3TlPlG9YP5DsWAdw4T7lzRZAc8kZ44iQP9hwG+7rLPzVpn7km5ySOv7JlmI2NBWDhPCeCm44QKF+4FXjGaJUMjOSP1hjRJ26S/1/tsiYe1xTkPOKlj1RneF05hFNJIxaAhU/EUIHs2KFJPMxD5xatylscU5JUbtxqSPyZb96d5rTPraRzZYnay1BcAauxegOxodp+dAXuis85cdH1I6Mecc4wMB75ohe6aoSLAsKvuRReni/4P3+6jfjqFg9kMhfjYwui57EDPuiR8gUnvR9VeNuMH/QwPERMqdjIGwGkgzR9IvZpEe11MQdRUU6CJVy6G3S7J+zTEdPo5cSKlG/wDfynQ2GiU9QnOsApoSn2Ob6lskiMnguuo6aBVYZeR9xA5HiuheDqewtDmam9DT6XMC+sGZw2GKfpSiAMtcjRUPmwxoz2a3N1t9iOK68OW4fQaxkZjwvsjUe7I5KlZTmtUBx3hmsIpoeun9EUp56zqFSPHTDU3k3KANDcSrk2ijAu8mi2WbNt4QM4VHVfzyK5CYbo+wyjhDjUTaqr4DSTIBM0eY2t6BOlDPTJswOyahegx2JSJYzc1RxITqnefoS0ms3/T/M7DX7UQID3G81XHb2jkZ6BZfX+6gHwyDx0FygtJR60BKZ5LCGMeAP7JdmgSn2ccBYbNymLQbeZZgeB9bhSHMM8cn76qUPcZ7tbqx5mLL2rlfji5deHSl7dgbTIaGF3Bqf/ZpsEeS3TqYvg0uky8YyhQLdyH/Vw2Bx6sZ5qjNdQN0FWdiUtXRseFxI7SvQgd+0cJ//3n7yEKl5kaGxdJ4CaQbBTksb4FWH7GNihizRe7E88enCNyQVKd8780/356Vvj5C343tFA='],
 [7,53,150000,90000,'71429523091691371/45000000000000000',313,250,297,100,13,2,5,'eJxtVIlx5DAMa2ULWM3wf2rxXP9tHEgll2Ry3seyLJIgAOnJ90v4/cKN6eN6vx6mrMQcxi4SzTv88f2DZSIa7Rryfpmai6ojSBs3rXYM1YsytVElwoMlMeRGdrbJyhrkUoUMFQjMLpQkIZOpL2Hq1qjHYkrEiHamklBMZYY6klhbqb1f3ayzlJIGHld0EN4/z3O4BplP0sMcGkikqXh0S4DEtDJrJu0CDbeK6RHPWkjunjKLqokwiKBITCNVGRqbKAIHIT1RvREGuCeqUay9Sac1oB4MWBc8ZBwBwwSWJuxMHiMCCQnqUMZks3gLy7RW4IsmgZJUSt2oycNQAhFssWWrq2KnpYR9RqrEd47wVlk/S4LcXqhBwz+Tcw0yMBk94jKx1lKnAPRZ1Vc/w3y1BhJfXUBfVm2cmdMWhB8k/IPPX1aa+ce2ZhjbNpoeiVCF7jIiA00XgE060Fwsm060RwYAEy/0UA4zzLO5i008/GmDyo0MUizPbFe7lKlxYDyZxUfaYKYdBbtJTaBaVdYa/liJj5nJ1iigZ5Q+rk2jEhw5dByBMgqqFuGuKDh/XD6vaCEyWehKhTu38mwXdt0g5eENbDcvePag3WcM6L1iqcKL06pZgn/7H7mXWdA/ahwObFhYkdaBiRZvAkXKhN+XmS02WBpGQqeOjxYvSyCbawuB/ekq19sWLndftSTxrB3ys2P3As/hwhJbiirJ1/97Kow94ay4VrSBZw6rQEjgu1pjJW/6xHEDZ/1q9HapPbCZcApkbwnsFHhoNajRmXE+CNs9GTztSgq/rdGSi2nrp7RvmEru0RNQz3b3KWGvfwNwS8/fv9/Pma+nO8L1F4onFew=']
];
for(const [n,p,ep,et,target,dn,dd,sn,sd,maxr,ma,mt,bytes] of charts){
 const q=21,gamma=R(10,21),C=JSON.parse(zlib.inflateSync(Buffer.from(bytes,'base64')));
 if(C[0]!==n||C[1]!==q)throw Error('chart identity');
 const [T,Y,U]=build(C,R(1,ep),R(1,et));
 const pair=check(bern(Y,1)),triple=check(bern(T,3),bern(determinant,3,true));
 if(show(U)!==target)throw Error('energy mismatch');
 const delta=add(mul(R(100,21),U),R(-15,2)),D=mul(R(64,3),delta),disp=R(dn,dd),sq=R(sn,sd);
 const f0=R(10-n,4*n*(n+2)),P0=p+10;
 if(cmp(add(mul(f0,R(P0**2)),R(-3*p,4)),R(15,2))!==0n||!lt(D,disp)||!lt(mul(R(n),disp),pow(sq,2)))throw Error('deficit or sqrt bound');
 let maxA=0,maxAB=0,maxBIf1=0;
 for(let A=0;A<=p*(p-1)/2;A++){
  if(cmp(mul(R(3,256),R(2*A)),delta)>0n)break;
  for(let B=0;B<=p*q&&cmp(mul(R(3,256),add(R(2*A),mul(R(2*B),gamma))),delta)<=0n;B++){maxA=Math.max(maxA,A);maxAB=Math.max(maxAB,A+B);if(A===1)maxBIf1=Math.max(maxBIf1,B);}
 }
 if(maxA!==ma||maxAB!==mt||(n===6&&maxBIf1!==1))throw Error('angular counts');
 const top=mul(add(R(2*p),sq),R(1,n));
 for(let r=maxr+1;r<=p;r++){
  let L=O,term=O;for(const [j,m]of[0,1,3,6,20,35].entries()){if(j>=r)break;term=mul(term,R(Math.max(0,p-r-m),j+1));L=add(L,term);}
  const tail=mul(disp,R(1,r-n)),upper2=mul(pow(top,2*n),pow(tail,r-n));if(!lt(upper2,pow(L,2)))throw Error('rank '+r);
 }
 console.log(JSON.stringify({n,p,q,energy:show(U),delta:show(delta),D:show(D),maxA,maxAB,rankAtMost:maxr,pair,triple}));
}
