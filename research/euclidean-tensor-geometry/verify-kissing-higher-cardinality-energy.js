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

function nearMargin(p,s,q,U,H){
 const h2=mul(H,H),div=(x,y)=>R(x[0]*y[1],x[1]*y[0]),sq=x=>mul(x,x),oneMinus=add(O,neg(h2));
 const A=sq(div(add(R(1,2),h2),oneMinus)),C=div(sq(add(R(1,2),H)),oneMinus),phi=x=>mul(x,add(x,R(-1,4)));
 return [R(3*s,4),mul(R(-s*s,q),U),mul(R(-p*(p-1)),phi(A)),mul(R(-2*p*s),phi(C))].reduce(add,Z);}
function tolerance(p,s,q,U){const D=10000000;let lo=0,hi=200000;if(cmp(nearMargin(p,s,q,U,R(0)),Z)<=0n)throw Error('no exact-pair contradiction');while(lo+1<hi){const a=(lo+hi)>>1;if(cmp(nearMargin(p,s,q,U,R(a,D)),Z)>0n)lo=a;else hi=a;}return lo;}

const inputs=[
[33,15,'eJw1VYlta0kMayUFxIDuo5bg99/GkhqvE/gN3ugkKfmvf3/cf3/wUPl+fn/+ylfm9wdHH/ewO5ql1d7x+/8Pph9X16DXp9JkO3HKmO0pnHw6xhHrY+nSQzsNQzKjHQLuverCJa3cR/kc3eBT4+KohNEjNJypts8LZ9N/zBPiaYny/v7+PloIqi3n2TqM1JHJt2VVDGFtNdWXQ2uSSMy4SF5frArt0DHtCnC5Smz18nhLu12NYT4B/11lR0Z/tuXIjQKlFK1N5lmrTO+1Eh3rfJWaY4jd3Vky/s1/dWq0KptRd77D9cJUF8kWWMP10ZKrk9J6pKgfznq8ZBkxBZVJaFVHnQWMZjnbroiM4qHwtMcrPXDmtzMRGndv+FXCjpBXKaFJRfuE2NR2018FqEg9xg7ADESbRiLmh8MV3NOKp6F5HYpwLbr3uSPx8VeFhg/E5+3V43gP9CrxtPCcJcxOYOsf3VG9DbmDqpJQtEVch+LAYqh2Q/JHLHGwJ7JGcXv9IyYpNejfTmsLMIZ5dXtPV7ttDAVARYIQueAys6+FtoNNq5pDMST7ImFgtu4KFIbeu4rVOlaQX2cqHwmtl4NtoyDA4fpKRR4eFILtJk6T4XqjI4g1VQwAGASZClmOMyh9pRhQpweSJIBSuXs6wdjfbACdJN4XQtWY+VOKIlAhEJkniKhh9R7qS07QWZsc3mvdGm9ByL3bcVBFQQNskoMSjasFLdhyNAw99qUHETH5qEy7BYESh/zhgtLJ71IRrIt5al/IqOr/4UUMssxEiD/gn0qTkpy5kQtD2ic2pxw/qOdIyaCt0uDmH1PsdsOHEcDfTP+/IDBxVwW5ZVB0H4GLcIjrdh0oFyg2H5IAC+rgMGCRCX0AaX9lGGJH6WdzqNY3B4dYvn2GJUEiJiZ8n3RzbuFiFIDrV/ycSSKO6QPFZ1gboFZu62ggwXfG+9aecrVCxSsE1wwm0NDtZ2xV7FEav4yYVeqV99n6ZgaSOkyxolCY3fpDZjvAliEXqOxRjUrU39KUWiyeA0ao/PlGhKripD1YYC8HulhsjddeLSzfeCwLjXngCnB64bZV0r/WSWWCXIg4brMaFmjc7x3CPBwg1qcy/HBgFJ8nv74nfP4DK3pqLQ==',1500000,150000,'24746907619329667','15000000000000000'],
[40,18,'eJwtVYmRAjEMa4UC2Jn4t2thrv82TnIWGAiJ40eSvb/6fvx8P/iR876+n59MWGKBj4iOi+3aW6zv9vv5g/ET08dOfz+PSJ2jFVweFTVRLMsPXHDlU9bhWGlr10kaIlLQ65MGN8bDmHP96VRzJ+oYN/SE8Xr01AY5vmFxZn8M4AhUirPf7yfHh6fpPA51bGembAh1a6ZkUebcMZGowoWwGmlz1rbpK5MbN0EsndaCuzntyF4aVTQuqam2CHZUEXC8FpoUYgEE/Wa7taeO7ZVygvyIH8Uf5lAeAINkoCaUousFWUg0PGnAdJPtdL3oxbLTGRoMn5WaOAEINmJCB0MHkgu3Yp9APCoVszuBl6yvqgxkJnYS0INwBNGMpZmmIxRKnFZCkTPG8tp9s0dZQIOVUTHMCiiDbpu9vyGyaku2btvgB9pZjBToEO4gGBQesCjqoiYc1vQRtwRbBiEr/kr4DHw3yl44E+pt5unSygohRK3pP3r4SQzl8GQj9GIuJykmk+qhf+BYpPrBv1sPYpRBw1uHZF+iB2zw0BMX4DLcV8bQKGCkOLRPxqpMu6Hys0UALzo1pMlwcxBNF5sAm1yNnoq67MbUikehKSi414OZy8rYgBq58EarnVVQxWHJA6U2dZFZ0hf6hsDzKiqSuWLjKrO9ZnYFx8MjTXSwyxJSocVVW5vNogCQmkoUQUeSIxCKKEhx8NdxI9jBYBKWRMkmRut2BbJo4pNauSGSLUHKgQGRQwPe3gUz7XeyQJ0tl0Mo4OyMAdW4lmggDzYjaLI11wRUceFmCzbLVIf6NHYigSwONEwjkNmvXSMXAM4OOAMGwIW24VpeHJLD5RKw6ZqxHx7yMkSBI1RsewPyLzQBjbuZHBAcRLRCp8PbmHbIdjBkV7a0YATV9lOusiOJGHMAPSuZRFLA/xWysCR+uxT0eekblWAGj2Wj5f2dIEuW9gxxOnpkZ8IAd92LDkWYtNyplQt56M5cjIu53mHbMdukED/bcrOundUpXTAa1c0eckT33/EHjR5c2A52JhLhxOtJ97I1pvy20xxtDV3cGgvDQ+9DZg6Gj62PfcpcbKEyU/C81n5W6J09eHOr9sGi0Ch6/ZIsmI9XOvjovcivd4XXP4x2Zik=',250000,40000,'16658530157187769','10000000000000000'],
[47,21,'eJw1VYmN4zAMbCUFxID4k7UE138bN0N5g+xGsCQ+89C/+n4cf/jKeT/fz0/G1O37wVrcZ6p23W5iscv3+w+Hn7Tyavl+HtFQawkuT03O4dOadi+Ee8I6JnDxQSDxTB6MHHdeKbfDrNjMMN+9PrZbJwI1PJopDNk2PChtyqedKOTxkDmeOPf7/fR0MoQqqkCD3WfYTWPFm1VnmH4my1mRTviGi8k0XGJvMXigi4W43DK1HM1tdRHGMuakKhauhqyIKmYedbQWH8ks5K5iC4Z0bKB6UIcCBPGbvYMLbxctJR8IO6j6xjjBas1tYRCAjOvhR9iFRZoCl8iz9UoKKatB91rbiYQQeIlpW1hqfBbCiCSkCJWJJ3pA0SzIQJMEekudjEs2IM49zepRNTvTRNRZeopg24ScRgFZaTyHJvEkbgDQtBWM2WrG+1xuAf9cksFREHFohPHQ5vDOHKAgC4iIKqlPu1RAdSurrKCCu7FPvhX6aaI56awI8hyI6R9j/ConjeHTSZ8h6Nl2BO0wb1YN+2pcAiqs7bSPHt0aIOzN2jIk01TXPo9Bx3wgDeETQTEoQ5Y6A5px5CoDblkPwGJbyZPzZx/agyCAwKsYkQGtK16oYBz9bwwE3JYNvBV3HZjwZtGsLEfGTyi22nwil3Wk83z12dk45nHW50A9e20IFUOKspKHvs6mVqvU3YUo4OplQyNgDuamFNbpoy5UAGywNTswrV51QqRrPbYKZVxVqJ9NhaQliu0xTJ6dSyPSV6rS+yAq7rxo+6OSolkhAIP9ZRYcArV+45YYfbrjwlzhn+UQR0hVlhEhoV14j2MMHTNtBjwyFysZ3WBQFycn+YVMoDm68U6n3CHhUDNsNG+OJ9Zbj0Lh/AUx7pwdDmTHF6BTnXouJUlGc4AmSoGY78xC1Xu0u6DRHZ7QF6bFOsuYWOHqFxtfNjkYNnNVsTGI9RjAuLBBGjRJUr0YPBD5UlCY6Ds94SfF2PKrNJiYboYAcIxzY28XjVwrY+aKurrUHS8IQNKhG8zh9X3DiTc4jInJoisAR6ytro3cVlNaCI6ej13WDl8KvvhAlYcjuWGmxU7hMB4/nFnrFi9OunzV4cFpgWAUHgbByEsnG4Dk9k2AlFDBbRUeX6ka3x2Y+3YhDuLvumMWHtrq3wxrnfc9iPfInItazlWTc347Xlh+7M7jXgLP0c0O5tv/1Mx/7wqf/+cqgpE=',300000,40000,'524322162503271','312500000000000'],
[56,25,'eJw9VYtt41AMW6UDNID+n1mC7r/GkbJxQdE4tp5EUaT87d+frN8ffKm8n9+fb5sU7uLSy2z296c6HTFZlnYP3r8/RH+qXcZx4KM2UrF3qSUTm7hcqxrnVUuLMN8nhnGDK1d3l+CR2TC9K8mOYJpMbWWYZbf58yy2ebB65G6EKyN0L3Djj3fDo4vZvt9vGGtOGZNn9JUr9+B5M7cx4mwNuxQSgZbQ/q6FlrFNlLB0xG2I4cs1hmQgWkwPmYmyTe8Qd1QcdJmzeSxZ6xU/In35lS2kQHWMPwEwJJjSx70TTSIgNy0uA8/HLrFbVBQZje4jNDxLi7URjQid5AcPdkItD0Mi0GNJLNDEHnpgbF6gt6AOMgXx1w6YEdxyceReeVn4pHkf0dsJ+AbinwFkie7RlKaXwlHbQbICbZTrpbg+XEkeUm/FI5fkVGzROuItvIoX0/ydkCGEcMeLulzx643zAjojkAFgQdLj5Cbdjm6YrUdD/ngccjVHcArAU2FIPH0Q1hcJEN6ztaeYHc7vFQk8MM8gHBwyUPX88NFetIqkW0hLEkciz1WFrH78IoW+FHw87NTdA5Gy6xa6ZrLgONKjbnua8h0xDhKiUBnz04I15nfPwQrFHflKBwacOgNC1U7rwCZo1Z+JFURel2GUdgKrsg88zBgt7BVhOYN22RQcutH7zHM74I6Hha2bDYBFniOBmvOH91Rz6S3YACXZYQh2R53tQsWbKRao/RGUNxMoRJinjwJxQm1BS/h9gzymZYCz3lHSBazSx/oH9Dq1nLr97CPkH7ktAWE1vOzXO81+Qs2LJ16j32EGDI42+CQUU9hbjHe/TQUayCd4KyooHJI4WsEKumJIYDVhoeV/v0JjZ+gCazdEqEioHTC2Zzg8iwks2OeMEBjQdDWVHHV0wAx5s8Bs4NAjGUQNhnjGJi64oQ+mFWDIiU8eWLiFpckFnLJYjA99WFfIjW0m/I/GbzNjhy+KHTJ4NLGbHslqG25iW3BrNpMTaYGUkIvGMSzctw++Ck4AdoUh597S27LRD1ACpjGP4uinq4K1wdgI5M49pnyL9D1a4JUnP7YbfYP3RZ7RFwSDXpSoK4LqGJ+8OrFeMPLyC2nKo+AwrPsbMAQwYPaJhpr1nISdhbfPU67j0mNBqLyJ6rYGXh14V9hzlP/eK3z+AXRbdIw=',2000000,125000,'2099404735107247','1250000000000000']
];
for(const [q,s,blob,ep,et,nu,de]of inputs){
 const M=JSON.parse(zlib.inflateSync(Buffer.from(blob,'base64')));if(M[0]!==7||M[1]!==q||M[2]!==7||M[3]!==100000000)throw Error('chart header');
 const [T,Y,U]=build(M,R(1,ep),R(1,et));if(cmp(U,R(nu,de))!==0n||cmp(U,R(3*q,4*s))>=0n)throw Error('wrong energy');
 const p=check(bern(Y,1),null),t=check(bern(T,3),bern(determinant,3,true));
 for(const P of (q<=40?[36,63]:[63])){const a=P-s,n=P===36?6:7;console.log({n,N:2*a+q,q,U:show(U),maxPairs:a-1,halfChordNumerator:tolerance(a,s,q,U),p:p.nodes,t:t.nodes});}
}
