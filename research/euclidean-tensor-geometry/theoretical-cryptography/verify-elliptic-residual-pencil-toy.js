const q=5,K=125, m=x=>(x%5+5)%5;
const vec=a=>[a%5,Math.floor(a/5)%5,Math.floor(a/25)];
const enc=a=>m(a[0])+5*m(a[1])+25*m(a[2]);
const add=(a,b)=>enc(vec(a).map((x,i)=>x+vec(b)[i]));
const neg=a=>enc(vec(a).map(x=>-x));
const mul=(a,b)=>{const x=vec(a),y=vec(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-2]-=z[i];z[i-3]-=z[i];}return enc(z);};
const pow=(a,n)=>{let r=1;while(n){if(n&1)r=mul(r,a);a=mul(a,a);n>>=1;}return r;};
const A=b=>{if(!b)throw Error("cubic numerator toy failure");};
for(let a=1;a<K;a++)A(pow(a,124)===1);

const plus=(P,Q)=>{
 if(P===null)return Q;if(Q===null)return P;
 const [x,y]=P,[u,v]=Q;
 if(x===u&&add(y,v)===0)return null;
 const L=x===u?mul(add(mul(3,mul(x,x)),1),pow(mul(2,y),123)):mul(add(v,neg(y)),pow(add(u,neg(x)),123));
 const X=add(add(mul(L,L),neg(x)),neg(u));
 return [X,add(mul(L,add(x,neg(X))),neg(y))];
};
const fr=(P)=>P===null?null:P.map(a=>pow(a,5));
const pts=[null];
for(let x=0;x<K;x++)for(let y=0;y<K;y++)if(mul(y,y)===add(add(pow(x,3),x),1))pts.push([x,y]);
const rational=P=>P===null||P.every(x=>x<5);
const sums=new Map();
for(const P of pts){if(rational(P))continue;
 const Q=fr(P), R=fr(Q);A(JSON.stringify(fr(R))===JSON.stringify(P));
 const tr=plus(plus(P,Q),R);A(rational(tr));
 const name=JSON.stringify(tr);sums.set(name,(sums.get(name)||0)+1);
}
A(pts.length===108&&pts.filter(rational).length===9);
A(JSON.stringify([...sums.values()].sort((a,b)=>a-b))==='[9,9,9,12,12,12,12,12,12]');
const D=t=>add(add(mul(4,pow(t,6)),pow(t,4)),add(mul(2,pow(t,2)),4));
let zeros=0;
for(let t=0;t<K;t++)if(D(t)===0){zeros++;A(mul(mul(4,t),add(add(pow(t,4),pow(t,2)),1))!==0);}
const irreducible=[];
for(let t=0;t<5;t++)if(Array.from({length:5},(_,x)=>x).every(x=>m(x**3-t*t*x*x+x+1)!==0))irreducible.push(t);
A(JSON.stringify(irreducible)==='[0,1,4]');
