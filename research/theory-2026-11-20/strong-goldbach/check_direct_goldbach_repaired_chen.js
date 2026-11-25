'use strict';
// Node.js; positive intervals at exact fixed scale.
const M=10n**26n,P=n=>[BigInt(n)*M,BigInt(n)*M],
A=(x,y)=>[x[0]+y[0],x[1]+y[1]],
S=(x,y)=>[x[0]-y[1],x[1]-y[0]],
C=(a,b)=>(a+b-1n)/b,
D=(x,y)=>{if(x[0]<0n||y[0]<=0n)throw Error("div");return [x[0]*M/y[1],C(x[1]*M,y[0])]},
F=(x,y)=>{if(x[0]<0n||y[0]<0n)throw Error("product");return [x[0]*y[0]/M,C(x[1]*y[1],M)]},
Q=(a,b)=>D(P(a),P(b)),Z=P(0),O=P(1),T=P(2),n=256;
function log(x,k=20){
 const a=S(x,O);if(a[0]<0n)a[0]=0n; // Log arguments are known >= 1.
 let r=D(a,A(x,O)),r2=F(r,r),p=r,s=Z;
 for(let j=0;j<k;j++){s=A(s,D(p,P(2*j+1)));p=F(p,r2)}
 return [2n*s[0],2n*(s[1]+D(p,F(P(2*k+1),S(O,r2)))[1])];
}
function chk(ok,label){if(!ok)throw Error(label)}
const lt=(x,y,label)=>chk(x[1]<y[0],label),gt=(x,y,label)=>chk(x[0]>y[1],label);
{
 let a=Q(100,1149),b=Q(50,309),t=S(Q(1,2),F(P(3),a)),c=S(Q(1,2),F(T,a)),d1=D(S(t,b),P(n)),d2=D(S(b,a),P(n));
 let I9=Z,I10=Z,I11=Z,J=Z;
 for(let j=0;j<n;j++){
  let u=A(b,F(d1,P(j))),x=A(a,F(d2,P(j))),y=A(x,d2),aY=S(D(O,a),D(A(O,log(D(y,a),12)),y));
  I9=A(I9,F(d1,D(log(D(S(S(O,u),t),t),12),F(u,S(O,u)))));
  I10=A(I10,F(d2,F(D(aY,x),log(D(b,x),12))));
  I11=A(I11,F(d2,F(D(aY,x),log(D(t,b),12))));
  J=A(J,F(d2,F(D(aY,x),log(D(t,S(c,y)),12))));
 }
 lt(I9,Q(417,1000),"I9");lt(I10,Q(57,1000),"I10");lt(I11,Q(133,1000),"I11");
 lt(J,Q(84,1000),"omitted R11");lt(D(F(T,log(Q(51,49))),Q(499,1000)),Q(161,1000),"seam");
}
{
 let a=Q(51,500),b=Q(1,3),d=Q(499,1000),k=S(d,F(P(3),a)),base=F(D(T,d),log(S(D(d,a),O)));
 let K=D(log(D(F(b,S(d,a)),F(a,S(d,b)))),d),U=Z,J=Z,d1=D(S(b,a),P(n)),d2=D(S(k,a),P(n));
 for(let j=0;j<n;j++){
  let x=A(a,F(d1,P(j))),y=A(a,F(d2,P(j))),r=S(D(S(d,y),a),P(3)),r2=F(r,r);
  let f=A(S(D(r2,P(4)),F(Q(7,72),F(r,r2))),D(F(r2,r2),P(96)));
  U=A(U,F(d2,D(f,F(y,S(d,y)))));
  J=A(J,F(d1,D(log(S(T,F(P(3),x))),F(x,S(O,x)))));
 }
 gt(base,Q(54467473642n,10000000000n),"base");
 lt(K,Q(4124506855n,1000000000n),"K");
 lt(U,Q(99586682n,1000000000n),"U");
 lt(D(J,d),Q(965830695n,1000000000n),"triple");
 gt(S(S(S(base,K),U),D(J,d)),Q(256,1000),"fallback");
}

console.log('directed Chen/Wu checks passed');
