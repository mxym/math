'use strict';
/* Exact synthetic finite-field probability identities, no live data. */
const assert=require('node:assert/strict');
let exact=0;
function ck(a,b){assert.deepEqual(a,b);exact++;}
function tr(a){assert(a);exact++;}
const seq=n=>Array.from({length:n},(_,j)=>j);
function boxes(n,d){let a=[[]];for(let j=0;j<d;j++)a=a.flatMap(v=>seq(n).map(i=>[...v,i]));return a;}
function field(n,mod){
  const q=1<<n;
  function mul(a,b){let v=0;while(b){if(b&1)v^=a;b>>=1;a<<=1;if(a&q)a^=mod;}return v;}
  function T(a){let s=0;for(let j=0;j<n;j++){s^=a;a=mul(a,a);}assert(s===0||s===1);return s;}
  const dot=(a,b)=>a.reduce((p,v,j)=>p^mul(v,b[j]),0);
  const char=(w,x)=>T(mul(w,x))?-1:1;
  return {q,mul,dot,char};
}
const F2=field(1,3),F4=field(2,7),F8=field(3,11),F16=field(4,19);
const sum=x=>x.reduce((a,b)=>a+b,0n);
const prod=x=>x.reduce((a,b)=>a*b,1n);
const hpow=(a,e)=>a**BigInt(e);
function hcoeff(f,w){return seq(f.q).map(t=>sum(w.map((a,j)=>BigInt(f.char(j,t))*a)));}
function asWeighted(f,k,h,numer){
  const q=f.q,V=boxes(q,k),W=hcoeff(f,numer),m=sum(numer),m2=m*m,S=sum(W.map(x=>x*x));
  const C=sum(numer.map(x=>x*x)),B4=sum(W.map(x=>x**4n));
  ck(S,BigInt(q)*C);
  const all=boxes(q**k,h);let first=0n,second=0n;
  for(const selection of all){
    const B=selection.map(i=>V[i]);
    const moduli=V.slice(1).map(w=>prod(w.map(x=>W[x]))*prod(B.map(v=>W[f.dot(w,v)])));
    const v=sum(moduli.map(x=>x*x));first+=v;second+=v*v;
    if(h===1&&k<=2){
      // Independent direct mass for one column and a product systematic source.
      const P=new Map();
      for(const a of V)for(const t of seq(q)){
        const y=a.map((x,j)=>x^f.mul(B[0][j],t)),key=y.join(',');
        P.set(key,(P.get(key)||0n)+prod(a.map(z=>numer[z]))*numer[t]);
      }
      for(let z=1;z<V.length;z++){
        const w=V[z],d=sum(V.map(y=>BigInt(f.char(f.dot(w,y),1))*(P.get(y.join(','))||0n)));
        ck(d,moduli[z-1]);
      }
    }
  }
  // First moment divided by q^(k h) m^(2(k+h)).
  ck(first*BigInt(q)**BigInt(h),BigInt(all.length)*(S**BigInt(k)-m2**BigInt(k))*S**BigInt(h));
  tr(second*BigInt(q)**BigInt(h)<=BigInt(all.length*(q**k-1)**2)*hpow(m,4*k)*B4**BigInt(h));
}
for(const [f,w] of [[F2,[3n,1n]],[F4,[4n,2n,0n,1n]],[F8,seq(8).map(j=>BigInt(j%3+1))]]){
  for(let h=0;h<=2;h++)asWeighted(f,1,h,w);
  asWeighted(f,2,1,w);
}
function subgroupFixture(f,DD,k){
  const {q,mul,dot,char}=f,D=new Set(DD);
  const H=seq(q).filter(w=>DD.every(x=>char(w,x)===1)),K=seq(q).filter(s=>s===0||DD.every(x=>D.has(mul(s,x))));
  ck(H.length*D.size,q);
  for(const a of K)for(const b of K){tr(K.includes(a^b));tr(K.includes(mul(a,b)));}
  const V=boxes(q,k),W=boxes(DD.length,k).slice(1).map(a=>a.map(i=>DD[i]));
  const masks=new Map(),mapClass=new Map();
  for(const w of W){
    const J=V.map((b,j)=>D.has(dot(w,b))?j:-1).filter(x=>x>=0),key=J.join(',');
    ck(J.length,D.size*q**(k-1));
    if(!masks.has(key)){masks.set(key,J);mapClass.set(key,[]);}
    mapClass.get(key).push(w);
  }
  ck(masks.size,(D.size**k-1)/(K.length-1));
  for(const [key,words] of mapClass){
    ck(words.length,K.length-1);
    tr(K.slice(1).every(s=>words.some(w=>w.every((x,i)=>x===mul(s,words[0][i])))));
    for(const [key2,J] of masks)if(key2!==key)tr(J.filter(j=>masks.get(key).includes(j)).length<D.size*q**(k-1));
  }
  // Add a small uniform mixture; Fourier support is preserved and all
  // surviving characters of one stabilizer line share the same amplitude.
  const numer=seq(q).map(x=>BigInt(3*q*(H.includes(x)?1:0)+H.length));
  const WQ=hcoeff(f,numer),m=sum(numer);
  ck(WQ[0],m);
  for(let w=1;w<q;w++)ck(WQ[w]*4n,D.has(w)?3n*m:0n);
  for(const B of boxes(V.length,2).slice(0,200).map(b=>b.map(i=>V[i]))){
    const survivors=[...masks.keys()].filter(key=>B.every(b=>masks.get(key).includes(V.findIndex(v=>v.every((x,i)=>x===b[i])))));
    if(survivors.length!==1)continue;
    const ws=mapClass.get(survivors[0]);
    const count=ws.map(w=>w.filter(x=>x!==0).length+B.filter(b=>dot(b,w)!==0).length);
    tr(count.every(x=>x===count[0]));
    // Distribution Fourier amplitudes equal a scaled indicator of that line.
    for(const w of V.slice(1)){
      const h=prod(w.map(x=>WQ[x]))*prod(B.map(b=>WQ[dot(b,w)]));
      if(ws.some(v=>w.every((x,i)=>x===v[i])))ck(h*4n**BigInt(count[0]),m**BigInt(k+2)*3n**BigInt(count[0]));
      else ck(h,0n);
    }
  }
  return K.length;
}
ck(subgroupFixture(F4,[0,1],2),2);
ck(subgroupFixture(F8,[0,1,2,3],2),2);
const sub4=seq(16).filter(x=>F16.mul(F16.mul(x,x),F16.mul(x,x))===x);
ck(sub4.length,4);ck(subgroupFixture(F16,sub4,1),4);
function bin(n,k){if(k<0||k>n)return 0n;let r=1n;for(let j=1;j<=k;j++)r=r*BigInt(n-j+1)/BigInt(j);return r;}
const abs=x=>x<0n?-x:x;
for(const q of [2,4])for(let n=0;n<=5;n++)for(const num of [0,1,2]){
  const d=2n,up=d+BigInt(q-1)*BigInt(num),down=d-BigInt(num),M=d**BigInt(n);
  const formula=sum(seq(n+1).map(j=>bin(n,j)*BigInt(q-1)**BigInt(n-j)*abs(up**BigInt(j)*down**BigInt(n-j)-M)));
  const brute=sum(boxes(q,n).map(w=>abs(prod(w.map(x=>x===0?up:down))-M)));
  ck(formula,brute);
  if(num===2)ck(brute,2n*M*(BigInt(q)**BigInt(n)-1n));
}
console.log('PASS: '+exact+' exact synthetic field and likelihood checks');
