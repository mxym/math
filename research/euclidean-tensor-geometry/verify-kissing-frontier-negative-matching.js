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


function direct(C,sl){
 const [T,Y,U]=build(C,Z,Z),q=C[1],V=plus(scale(T,R(3*(q-2))),P(0,mul(R(3),sl)));for(const[i,v]of Y){for(const k of[i,32*i,1024*i])put(V,k,v);}
 const c=check(bern(V,3),bern(determinant,3,true));return [add(U,mul(R(q-1),sl)),c];
}

const rf=(v,w=1n)=>R(v,w),inv=x=>R(x[1],x[0]),sub=(x,y)=>add(x,neg(y)),sq=x=>mul(x,x),div=(x,y)=>mul(x,inv(y)),maxQ=(x,y)=>cmp(x,y)>0n?x:y,minQ=(x,y)=>cmp(x,y)<0n?x:y;
function pentagon(M=256){
 // j=floor(M beta/(pi/3)). Alternating Taylor and pi>333/106.
 const T=3*M-4,den=1000000n,weight=[];
 for(let j=0;j<=M;j++){const x=R(111*j,106*M),v=sq(x),z=add(sub(O,mul(v,R(1,2))),mul(sq(v),R(1,24))),z2=sq(z),w=mul(z2,sub(z2,R(1,4)));weight.push(Number(-divfloor(-w[0]*den,w[1])));}
 const cap=T+1;let best=-1;
 for(let fst=Math.ceil(T/5);fst<=M;fst++){
  const W=(fst+1)*cap;let A=new Int32Array(W);A.fill(-100000000);A[fst*cap+fst]=weight[fst];
  for(let k=1;k<5;k++){
   const C=new Int32Array(W);C.fill(-100000000);let mx=new Int32Array(cap);mx.fill(-100000000);
   for(let last=0;last<=fst;last++){
    let lo=Math.max(0,M-1-last);if(last===0){for(let u=lo;u<=fst;u++)for(let h=0;h<cap;h++)mx[h]=Math.max(mx[h],A[u*cap+h]);}
    else if(lo<=fst&&lo!==Math.max(0,M-last))for(let h=0;h<cap;h++)mx[h]=Math.max(mx[h],A[lo*cap+h]);
    const base=last*cap,w=weight[last];for(let h=0;h<cap;h++)if(mx[h]>=0){let t=Math.min(T,h+last);C[base+t]=Math.max(C[base+t],mx[h]+w);}
   }A=C;
  }
  for(let last=Math.max(0,M-1-fst);last<=fst;last++)best=Math.max(best,A[last*cap+T]);
 }
 if(best>1562500)throw Error('pentagon cost '+best);return best;
}

const charts=[[4,20000,"150015001/100000000","eJylUFmuAzEIu8ocYEbCmPUso3f/a5SklarqLT8PZcHBYMid52HnUecBedl53JAikuPOUorSOjb4WF9DvahI8/bS4HlcMZc4nZAe6JmEhbnAFxQGHBHEihpcXTpde+VypEbMpxYGKsMqyw07F6GsHmrZIkMMtBTTyq0rUiDDdyUT7WA5NzWF7T1NzBBXRmZPYSyN6VVVSl8lR4Caoku9StDKPUWjs1tWtqg6dUYHE9Y6rd33vb7iz72O/zB+j/4c+f76+fJGT2/sAcggc5E="],
[5,20000,"7500999957082831/5000000000000000","eJx9UtuNxEAIayUFJBLvRy3R9t/GGTa7uo/TRRNpBMbYMHeeh+9her7zuPH/d15/QBDjEOdScN33fYWex8XOfR6h7DZ5DRN/hyPCHp4mi5TzEE72gKDLosNjkKoWQjHIqxkcQiqDSHOzoRJJtenCrJlgeFgvZ5OhvViFaNsSGrPlxlzQdIllIgpBqyzReRpQE+iQyGbOj+cy13Um2hE5t3ZcV3VJk/ZroOsrxuQgqCppBuCdVaNJktLp3R9KkWsmX2uwGJhPDao0qtYmaVl8vXF6Vg+lpfQaomYxnaRmicLPgFEHIQ6+yQSpQuHAjUvWMVbWGQ+xY37kcxGjpNFgkOw5GmI2wfz1tzO5mNtb176hjfDndWw2sFpoxeCAInvXXtHEwcOuJIkB+u8iaEPNNoc9I+qnbrOCdWH18Q5lRePNvPD9ALREj6Y="],
[6,20000,"3750625000053403/2500000000000000","eJx9UmtuhjAMuwoHoFLej7Mg7n+NOYXt249pCKo2TRzb4crziPPw82B6n/O48P333n+kIGZt2VW4vC4DqGK7QrAoFp7QYlH+lK9io5xLZvfq8xAXbkNE2COsa5IZmWJg6iqeg6pAG9DVEiKDIEZRwvoBZ1fOKWWSSh2JnJHdswvKrNxKFqpzWjJCnbvAqXzaUGU4rooEnfMXOFWV8mCCZCDiEk4ECZmtrffkTvIaqkmGVCXVJnRQ8DfrkaXEiPtkp7zNkzi2dZ6CFqJOHkwDHZ3mLw2uyKqpAQFzQQvHKsbboTLpVyGbK2Iu0PfYJ+W9DXGDtJlVwdlvZLRmnGfnjnnEVBvDtdoxmBjej0S1cYq156TZOWWWmFTUNsx8u1Ayh4gU0z3QaA2SB2QZsoIez4dl/Axy/wAa5lbDoisbul5792UVddDrOCwxML/xfAE7FJK4"],
[7,20000,"15004523369195719/10000000000000000","eJx9kutthEAMhFuhAFby+1HL6fpvI2NzSf5EQYBWy/jzeJZX3hduvy+mz3VfLzz/3e8/JNjrFlUWfHy9TgNpeI5Ugd/CaCHGSo3NtmryX85Rxecqo3GinVRwxZ0szjG6g/pjgVcVlq5VU6KMKl4kV1sv88gQ70toHXCgF7YCYFNoOUGm1NFuY4FFs1klJsBay6Rz3MNClYxyM5r+tP2sQbgv5UgD3LmcWd+jnKEOO2VNCcBGsyjY6RlDNMKQxWiZZodbvNZrh4ags4ZyT1ZCbCWRKx4FkbLNgLYDjxUpUR+7ypVh+klh0R1wsnXSHDIxa/IcE0gV6PsTL4JynXPLmqyG522xZGC5op/5YFp07R+N7mZdCAeGrU/v6G/1cXuyhHOrsBUgxWlZkrZunXz/DOFWZ3kqwZAHXObw/9kNHL7lG9cXSMeNCQ=="],
[8,20000,"15031606412897291/10000000000000000","eJx9UutpxkAMWyUD5MDvxyzh23+Nyk5L/5QeCQRblmRdnryvui+/L6bvc18P3v+ezx8Q1CoscNB8nsMO2moDMaPPlWF9X6LSFpA7zB2W/cvFU+zqFrmvMG/dARbPrhycrk0FZ7biUyzdMMZaLlmon8AY249DDlulAFrViXKVoUsMbrYgCOmgjyCJozGOT9sMlOcMWlZZwdMR4K1r4YOuAImhCb9JSSuWxWmQMZZoss+gn9lNiLlsTVqLNRhMoohiFzdVkjUuvWpwya+pctZ3sCl4bkhCyFh94CyzqWYzjUxWe+quLYI01ngAr7nsx7V7zLu008ah3jYw80iuSVaxZ76Xk7QtMmuCG21httdWidIogQCJ5veqDVVeJQ23ao29O1V5CQ+Ml8gPGlLIaxcpdZYFE5Xxi8AflbbtziIH25arWhDMB+cLr0KOxA=="],
[9,20000,"15072396825682247/10000000000000000","eJx9UdmtpVAMa4UCQMrmLLWg238bzwE+R4NA4uQ4ju3cdR5zHjgPle85j5vf/97fPyCslU+rNS/vuzTO49Igt4Z5coxbVbRvWTVRujSX8oytiVQ1m4A0GzsPc5UZ9YXxL8+jlcicdumlTdMyEl+BbJQ9fNiC5hJoAyqrw3ocwRv1kVCdB+ok4KUv2XA2D+BP1EMxqSR4NTrnFkBOD/c9Xaau7WxxjCHyt8hNhehYfyuX6pulkaLd2buSaHYuGEpLLEitACs4iFVwcMnmJWUCfWwtkrbZvIJTI4wlE0fn0lxmynGfXq6BpQyZzf+ChDGF8aG5XQg0Gv6skaM2QKP9NXOFAHBOh/TAdlvMxDTlNeiFqXrj23W3vV7ap/IhpHv50tCqMenHgXHoxCdvlNt/ISJpb+OyzXytlNqM5sfnD+w/iMA="],
[10,20000,"7560160700981123/5000000000000000","eJx9Utmt5DAMa2UKmACSqLOWYPpv41FOPhdr5IJNkRSVu74fle8n9vWu7+fm/b/r9w8I93xgrc7D+77KSIkYPs0mCLkcElAqXimCtpemuaHSI2vkqpFK2rls0hp1UAC+H0ORLbRibEuSjm2w0DLvPrautrOjK9yNdn64QtG6RZFqmr5Q9Vy9UKxTaC5rTEX3WoqKsjnq4TS0x2jWk9ASkr5CQIRk/BZ3H4UchRCTAdFgoSmVqvFwulgt2HAsAuYkrha4vE6L8oSZ2tP9MThe8yhqZRpTZGlXpRwXYDp5AnCvjS8jJrfBkHbjUFBSVpujRFbEyeBpFdmmmB0R+9Mmuthq779wKWXC7ekwZc78csaPtxhi1sgM4mHEiUFkYvTYV8XbPLnepEo45nrjleo+3pmXdsqDGUs7LXEyDAfzbneRsH9cf8N7jZc="],
[11,20000,"3793356371707433/2500000000000000","eJx9UtuN4zAQayUFxMC8H7UE6b+NJWXffS3WiGOb4syQlD79fqm+X4mHPNf79cH91+/7CwVYdKeaY/HzUXu/LlP0vbRn+GEamHRFWLUSGffZp9e1uL0gY6oiWFZmWejmElm6TuaFlbypw8eYp5Mc5RGFoYqazv9da+mMoi6PCcGL1QZGkxo7HkqyMgc7/yJHdS2DudJ7tIh4t+e/zmG3w3Zq7bSAIxMoVgDe5lL9JZlsixJnQUhNqZw4ykcTVdNDnsEu8d3B3IqcVRaoZCGXUM9eO3lZk+iSrcc8hk4eibZiIvCcEqszd2bOxdRUOWKxD6wz7AIdm7rK3DHMLgPytaTI5HTjXnXFaKO8Ddy4nYU3WZNeW0TAgnkTnIQOAhnCmNS2wuvWjkR5DHbbnoQuZILkq7MjjRDT9DLZ4/dSRQ6nT/H43FUbHWdZ0UsQwgNj+23ni+sH3tWS3w=="],
[12,20000,"1903868816718591/1250000000000000","eJx9UskNpEAMTIUAaMn3EQua/NPYsmF/q0Uz0A3luuDJ+2K5L8eFvuO+Hvz/9/v9A4J7J9qVQfU8zxFcJe2+sjuGvTMZGA9hs11JWFB/ZAfQwsxhzowGwDrbeB5pR3VxDbTvq0NBqJFYa1ZazVhUepLs0so54i8z9uMARnAuD5qBcBgqEB0hE2HKgZ+dVx5/lh6j1l454cS0+Y1gRSmLxz4yeH1TYNpYuKGqJAg+ztQlqe03+GeRBp+EvCHU7LQeqlu156l4Q8EHzvAIz0yylpFqAmLKkz2GOwsiuW/EZEISUm1n1BAdQmlW4neppt663EdrCsFrYNLhcm5tyPU4l1xXGl22RaZOV8rh/LZjJr75kD+kZBsLRktv0oam0KuEkPg2eCMpXNm+ylMK7a8XDzcYnY1qar31Fr7K+CAFybcVFUF//d2Gw3L/4fgDKzaQwA=="],
[13,20000,"15292470594234823/10000000000000000","eJx9UtltxTAMW+UNEAO6j1mCt/8apZT0r2iQILZESyTlO68P6/Vx/Oh9rs+N77/3+wcEscPZlIVy930fRvSooHYJQslijEiol6XNilxU/S0GYE+eOZHv6xNkngs0caagHCT20rZsY06Zlve2LmUaKVh6Jbm9hQ/6o70BxR2kDq0eTNIDFiGcq2Vxpr90Dm9Lwc6JeLbhbJK+pCNZ+Rcu6ttCJ2mhWYFgkiIxzCm8Lb4Dv48suawaQuYexDWhhm1SU4fDRKRk8GqELIjmzMeVRqfAFVPttbZUS2uwTGNJpdF4c4Qd3k1B8erKXKUp4Cc7vBMpyy80duHhMRKYA2XXGS5mL10bWXYQkuHWvSMpxZExhNshamsQ3M1XbMRwQrBrplViuVRPWT+dRwOZGFE/dpKv2Wk+aiKyeo12kxXAFrV/yqS3jdpgHZOP8IeqA4ywcD79cPGeW9DxTiIdg1kwG07Cww1DeJgD8/3+AIWCnd4="],
[14,20000,"3071258142287641/2000000000000000","eJx9UtmthEAMa2UL2JFyH7Ug+m9jncDn00OcGePYzlz5/bB9P44Hvcf3c+H677z/gKB2QjyKQHld13FGxbBkyihlBNNgVK298Mak2Zb1sg1c5sbspAJEaZbp/GTlTiYLlcESltOHVzQtli4SPVSGplhdKF7mYzFVD8WfZRQKu8lpnNvUuohaBn30JT/iVPgIilzZnEo8NJ3pprZoGcICvKeDqdvEJ63CNiTGamh0D/habyYOTwgcujt8Sl2WJGtBg9B983XrAG+Tw2Sw8XyKiGvVCFKjQpbrkSdm9pb2YZQALtdElCFmm1etFpZc3UwZU3TqJzwv9cjx0Y++wxWpQr6RS/RQpLv0+qKOGDxGDsvPjNwQkb9ejWyWGwHYaqyAfiWJlF4R3Nm5kRAJb8mQGujVvIgfoqM+I8EGwK6hZ/4+Gad3rbgzUnaPaNIbdQkEbhMR7TB5y1kYPpjv+weSpphn"],
[15,20000,"3084513065368361/2000000000000000","eJx9UtuNwzAMW6UD1ID1lmYJsv8aRzq9fh2uSJ3AoimS8lXvl8T7hUf25/d+Xfj/99x/QLC3ukS0E9XrWpIgXcE1fGOt8EJtZVuq4swSNcmZX7407M2wsGtHANwV08r9sGycVGKTqtlnfLCqim0yS2mmJhlMKmd/qZfLgzCyShbY8VFVrUOdWoMAJohfILAHD33s0zhHVErFViURJE7J4V9ML5vJRdKpTaeARIkwqvdE45Cb8KuPw0Yaw2yiXM+WS5cJ2VXK97gRHmZU0GECdI035WmFah0s3lk+xEowGXiPk7R27PBPMkhP6cE8IHb8KJftDBPxeDKZhaKP8FLkfgQiM0TaJqfBtJM4NKyEbGW15Vg0m12slpbM5GNWo5rlDHd/4pUzNdtl7MEty+OKchC1PTNGX+rYMfrhsuOucCckn+B5u1Ra6wwCN+XMOhODPCeQZxynIuLl3wkI/AVY7/sHq3SahQ=="],
[16,20000,"15491374541827757/10000000000000000","eJx9kdmNIzEMRFNxAG6A9xGL4fzT2Cp1z34NxrBhSiqSj8VPv19a71fiT57P+/XB76/v9xcJ7q4x0UrH6+ejjttqHK4NQ/0WDcWp01VrEKnFZvk85TQIQYmKWQZSVzK9DVcZ0VFZ1F5Jau24ayTedXOleB7bkGIVl43MMqbwbM2Sl1WzWVl3LLDG0YEtDFFW5NGfBKUgxge0XbvIu8p7O/pQTpjPjxuquXYm4Kt3jeAImp0iWfSaVX0p/yxtmRBhkAItZ2rf2r4hdya7KY4y0GQJF3WlgpK4XsifTFaqnNR70AYrTBFzqK3YHZULc3WRP9DJR/0YCc+Yj4W0ElpNz5A6HpieIR4QHxD182jeKgkkDy/dpftYThwSl26Te8jJsyA9PXRdvQgesSbxuIZ7yrrHhuN5jBSq/d8zWDDaWZ/nHOMh0UdBwzP3+FsZXTQvPVXlcVpterGU2xyR+PEUS78V2HkvowXf1AOPuQ36Lz7/AAK4oMg="],
[17,10000,"15527458603664149/10000000000000000","eJx9VG2u40AIu8o7wKsE5vss1d7/GmtIfq42ajrpBLDBnn7r90d5Jxd5r9+fL+//ff78O4TbH+QUsp0R3+9HxbinHbKLxe+Pqw74w2X461MlDegmmho38dbOJYbmC6tNTowuNbWKArZsuY1Cjo3nAowwwcUJwHI6XNznsJvlB6T1iQzJLnuBmHS5xmc32RCV0ikSqLaA1NGVnOzepA/jY7bFj2q73moeRK2qLZY97rVtQmFFwMtb0i16cHgmE1bFAihIyq0hR7h9vGQubxtxwpOZ5wGoTC2eZd1oXbPtwWuOJf5s3vezFK3zocjZJpgM3QHsK2AMmVcw0QjYwxOzU/A6qjm9aVZmq0l0R8rsIKsGJXU5xYzx0JV4OL3rblyA5YdpQT+g3DP0IaXn9Vriq7SD1+YRanVIyvuQx4S6VhxUn4zG8SjWJCmiuqrpWNczfrpr7eVhzhKbRiuSk0FlGVHicuWGsh3JZQs+bZ0PoaCR7wwVUeuj3lcdRhZb2bKjabINWjfW+NotkgY9w3qbG3V5FDx194TdsJ3MJ7blaE/HXNSzk/p4KEqirnd2Dk7kbD4Sq0zjBOA5IMpNLAs7n5czY7LuBX2ofV7j6UK1PnwyVlFdmSnGw9gSggy8jM8VWv3YG7i2VQLhTwwPy3KZ/fvwzjMitjNTf4js192vHYPm7ucsNE/F2BvG6y+LAuVA"],
[18,20000,"15633783274692763/10000000000000000","eJx9Uluu7DAI20oX0EqYd9Yymv1v4xg6n1c3atWGGGNMPnVf6PsKfuS37uvD93/P9x8Qxp44ggrj6efjCkZs6FIDyk1rVCQDD9DZqj1Ez+DmzVNov6/WsqM+fOpW5TmwOMuXSaURIZvVHWV++KsVruW6jKoTggDTVpmmDe1JL19sOUzyxUqzf8UhJK3PZKa5io/Qw5DIGSTkMNm16ZVaA1RighCf3rwlSvQ7yPHmqVRgyMKSYGKQjo4eAScjLWJpMfkF2YYJHsces2Ih8FddQ2oVjHi2ozbmaFFrb+vm6TK87lBKk58JrwueMpILljX7cikx2ymwGmpVDIQplivHkBS0VgQ92zw5eVB4O5yi2NoUmmMAotjy6nx8ZsWbwDLrDQ6Ty/bMvGIbVDB1KMTAicyhtuW4kIdMS0oVSfPeom1URFNperxXx4yF4vRvG2fsBUtx5G+OdssWjhbnZXmjwaEfP1+uP5VUmg0="],
[19,20000,"981755076936669/625000000000000","eJx9ktltxDAMRFvZAiyA91GLsf23kSFtID9BFmtYFp+GQ1J3Xh/u6+N40fu7Pjee//7fPxDsHQ2yZEX0vj2wkcnXJz1iPsq9TLBxkIpJOF+dI3jalRRu0ko54OdYhXXlZhMaJml8lmb0qDSlSKyAhFn0ooc5NofgxdYZDCTFqWtkJcQ4upb1QkyrgWbJyJ9Q9lCbdJVuLgO6gTMdQKVtFCWrMyeVhYW2fQe8p+CqqA0UJAheYZx0kzcO16N5II40Bj+IuMDiNEdZ0yInXzW3PEZNdIpiMAVc3HB48WhzGgXTxlHq4Zli5lBdNkYiprWHUZejzOkLpJY8QZARhQ4VFpXSWxUrOrWDYCaHp34LtHVC0SMpNJ2vhzfT35lKgeMojRrQxL1FNn56D3jtpKRROj/+oui5FnMnmLOmRLcsmlbNaJu4+XWCVXPs1FnSdW8KXEi9XhU99VllR5XRs2uoxhkf3+8P3fKZ7Q=="],
[20,20000,"789178042386081/500000000000000","eJx9Utut7DAIbCUFZCWGN7Wstv82zuDk8+pGiWJjYB74W/elcl9xX5D3ua8vv/+9v3+kMPZRrVEfnn6/Pmwd6vdVKtY87Z6oiF0NZMq3zce4Z9IHEjVIpiNtYkMe5aWJzStdpgHyLHXFVozNmOhZloSIno5YBjrCXsiWMiZnjLgvtoZEZjzgWrr4Rtr31WjbXVrAsYyzfdwPfusGoN4Ua2XaZKg5VBKHqoy2/DaVDFajlzg5uzcobMkzVxZNJCUxm6tZC4mYXLvMfZloVbRudQNcHF26DkC3WI/XnR0sDkiVLDu3FHAER1ogNhZVoB0p5wfPnjKyAFl5Phz25KMOuJxVobqJAc4jj0Gg8DSPV5/j4KEzn0nBtrwOcLVt+zSKWlK0sOWR8Imuwz3p4PGaAAQ5h1bHCl4RoeLT1JITsQcUWCRg1FLxDPpBIPgLHbou8sZ468tVp98LBBhH/0QtzKjhx+cPZnqaWQ=="]];
const cap=[Z,R(3,4),R(3,2),O];
for(const [q,den,target,bytes]of charts){
 const C=JSON.parse(zlib.inflateSync(Buffer.from(bytes,'base64')));if(C[0]!==7||C[1]!==q)throw Error('chart');
 const[U,c]=direct(C,R(1,den));if(show(U)!==target)throw Error('bound');cap[q]=R(-divfloor(-U[0]*10000n,U[1]),10000n);
 console.log('energy',q,show(U),c.nodes);
}
const pc=pentagon(256);if(pc>1550000)throw Error('five-cycle cap'); // (15/4+2*1.55)/25 = .274
function types(k){
 if(k===1)return [[R(3,4),O]];
 if(k===3)return [[R(3,8),O]];
 const b=k>>1;
 return [[k===5?R(137,500):mul(cap[k],R(1,k)),R(b,k)],[R(3,4*(b+1)),O]];
}
function profiles(s,cb){let A=[];function rec(i){if(i!==s.length){for(const t of types(s[i])){A.push(t);rec(i+1);A.pop();}return;}
 const p=A.map(t=>inv(t[0])),S=p.reduce(add,Z),S2=sq(S);let c=Z,full=Z,ms=O;
 for(let i=1;i<p.length;i++)for(let j=0;j<i;j++){const w=div(mul(R(2),mul(p[i],p[j])),S2);c=add(c,mul(w,minQ(A[i][1],A[j][1])));full=add(full,w);ms=minQ(ms,w);}
 c=minQ(c,R(1,2));if(p.length===3)c=minQ(c,sub(full,ms));cb(inv(S),c);
 }rec(0);}
function part(k,lo,S,cb){if(k===0)return cb(S);for(let j=lo;j<=k;j++){S.push(j);part(k-j,j,S,cb);S.pop();}}
const kappa=R(3,40),phis=a=>{const x=sq(a);return mul(x,sub(x,R(1,4)));},marks=[0,657,652,645,638,630,619,608,595,580,540],bar=[];
for(let m=1;m<=10;m++)bar[m]=phis(R(marks[m],1000));
let ncases=Array(11).fill(0),pcases=0;
for(let del=0;del<=10;del++)part(21-del,1,[],S=>{
 const def=S.filter(k=>k%2).length-del;if(def<3)return;
 profiles(S,(self,edge)=>{for(let m=1;m<=10;m++)if(def>=23-2*m){
  ncases[m]++;if(cmp(add(self,mul(edge,bar[m])),kappa)>=0n)throw Error('unresolved Tutte partition: '+[del,...S,m]);
 }});
});
for(let a=1;a<=10;a++)profiles([a,21-a],(self,edge)=>{pcases++;if(cmp(add(self,mul(edge,phis(R(522,1000)))),kappa)>=0n)throw Error('connectivity cut '+a);});
console.log('complete',JSON.stringify({pentagon:pc,cutProfiles:pcases,barrierProfiles:ncases.slice(1),thresholdsPerThousand:marks.slice(1)}));
