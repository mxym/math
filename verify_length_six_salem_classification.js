"use strict";
const assert=require("node:assert/strict");
const dd=[];for(let i=1;i<=60;i++)if(60%i===0)dd.push(i);
function divpoly(f,b){
 f=f.slice();const q=new Array(f.length-b.length+1).fill(0);
 for(let i=q.length-1;i>=0;i--){
  q[i]=f[i+b.length-1];
  for(let j=0;j<b.length;j++)f[i+j]-=q[i]*b[j];
 }
 assert(f.every(x=>!x));return q;
}
const tbl=new Map();
for(const d of dd){
 let cur=new Array(d+1).fill(0);cur[0]=-1;cur[d]=1;
 for(const [m,obj] of tbl)if(d%m===0)cur=divpoly(cur,obj.g);
 const sz=cur.length-1;
 const z=new Array(sz).fill(0);z[0]=1;
 const ww=[z];
 for(let k=1;k<d;k++){
  const w=ww[k-1], b=w[sz-1], y=[];
  for(let i=0;i<sz;i++)y.push((i>0?w[i-1]:0)-b*cur[i]);
  ww.push(y);
 }
 assert(ww.every(w=>w.every(v=>Math.abs(v)<=3)));
 tbl.set(d,{g:cur,sz,ww});
}
const tab=[new Array(60**3),new Array(60**3)];
const rowIdx=(n,s,t)=>(n%60)*3600+(s%60)*60+t%60;
function gcd(a,b){while(b){const c=a%b;a=b;b=c;}return a;}
for(let sg=0;sg<=1;sg++){
 const e=sg===0?1:-1;
 for(let n=0;n<60;n++)for(let s=0;s<60;s++)for(let t=0;t<60;t++){
  if(gcd(gcd(gcd(n,s),t),60)!==1)continue;
  const keys=[n,0,n-s+60,s,n-t+60,t];
  let I=(n*60+s)*60+t,dz=[];
  for(const [m,{sz:d,ww}] of tbl){
   let w=keys.map(k=>ww[k%m]);
   let yes=true;
   for(let i=0;i<d;i++)if(w[0][i]+e*w[1][i]-w[2][i]-e*w[3][i]-w[4][i]-e*w[5][i]){yes=false;break;}
   if(yes)dz.push(m);
  }
  tab[sg][I]=dz;
 }
}
function pcount(a,b,s,t){
 const d=gcd(a,b),u=a/d,v=b/d;
 const z=u%2?s:t;
 if((u%2?z:1)!==s||(v%2?z:1)!==t)return 0;
 const d0=gcd(d,60);
 return d-((z===1||(60/d0)%2===0)?d0:0);
}
function trcount(a,b,s,t){
 const d=gcd(a,b),u=a/d,v=b/d;
 // Both assigned phases are signed primitive cube roots, and swapped by conjugation.
 if((u+v)%3!==0 || u%3===0)return 0;
 const z=u%2?s:t;
 if((u%2?z:1)!==s||(v%2?z:1)!==t)return 0;
 const d0=gcd(d,60);
 const order=z===1?3:6;
 return 2*(d-((60/d0)%order===0?d0:0));
}
function ten(n,s,t,e){
 let y=n-2*s,z=n-2*t;
 return [
  pcount(n,t-s,-e,-1), pcount(n,n-s-t,-e,-e), 
  pcount(y,t,-e,1), pcount(y,n-t,-e,e),
  pcount(z,s,-e,1), pcount(z,n-s,-e,e), 
  trcount(s,t,-1,-1), trcount(s,n-t,-1,-e), 
  trcount(n-s,t,-e,-1), trcount(n-s,n-t,-e,-e)
 ];
}
function exceptional(n,s,t,e){
 const z=[n,0,n-s,s,n-t,t];
 const es=[1,e,-1,-e,-1,-e];
 let total=0;
 for(const m of tab[e===1?0:1][rowIdx(n,s,t)]){
  const {sz,ww}=tbl.get(m);
  const v=z.map(x=>ww[x%m]);const pow=[1,1,1,1,1,1];
  let mult=0;
  for(let k=1;;k++){
   assert(k<=5,"multiplicity exceeds Vandermonde bound");
   mult++;
   for(let i=0;i<6;i++){
    pow[i]*=z[i];assert(Number.isSafeInteger(pow[i]));
   }
   let eq=true;
   for(let i=0;i<sz;i++){
    let sum=0;
    for(let j=0;j<6;j++)sum+=es[j]*pow[j]*v[j][i];
    assert(Number.isSafeInteger(sum));
    if(sum!==0){eq=false;break;}
   }
   if(!eq)break;
  }
  assert(mult<=5);
  total+=mult*sz;
 }
 return total;
}

function coefficients(n,s,t,e){
 const f=new Array(n+1).fill(0);
 for(const [j,c] of [[n,1],[0,e],[n-s,-1],[s,-e],[n-t,-1],[t,-e]])f[j]+=c;
 return f;
}
function split(f,b){
 // Exact monic long division; returns the quotient if and only if the
 // remainder vanishes. Used by the independent small-case check.
 if(f.length<b.length)return null;
 const a=f.slice(),q=new Array(f.length-b.length+1).fill(0);
 for(let i=q.length-1;i>=0;i--){
  q[i]=a[i+b.length-1];
  for(let j=0;j<b.length;j++){
   a[i+j]-=q[i]*b[j];
   assert(Number.isSafeInteger(a[i+j]));
  }
 }
 return a.every(x=>!x)?q:null;
}
function smallControl(){
 // Independently count all cyclotomic factors by polynomial long
 // division without using the ten directions or derivative criterion.
 const tab=new Map(), C=[];
 const N0=14, cap=2*N0*N0;
 for(let d=1;d<=cap;d++){
  let f=new Array(d+1).fill(0);f[0]=-1;f[d]=1;
  for(const [j,g] of tab)if(d%j===0){
   f=split(f,g);assert(f,"division of x^d-1");
  }
  tab.set(d,f);
  if(f.length<=N0+1)C.push(f);
 }
 let checked=0;
 for(let n=3;n<=N0;n++)for(let s=1;s<=n/2;s++)for(let t=s;t<=n/2;t++)for(const e of [1,-1]){
  if(gcd(gcd(n,s),t)!==1||(e===-1&&2*(s+t)>=n))continue;
  let f=coefficients(n,s,t,e),degree=0;
  for(const h of C){
   while(true){
    const q=split(f,h);
    if(q===null)break;
    f=q;degree+=h.length-1;
   }
  }
  const exact=exceptional(n,s,t,e)+ten(n,s,t,e).reduce((a,b)=>a+b,0);
  assert.equal(exact,degree,JSON.stringify([n,s,t,e]));
  checked++;
 }
 console.log("Direct small cyclotomic-factor controls:",checked);
}

function proofRange(){
 const capN=649;
 const B100=[1n],B101=[1n],P27=[1n],P16=[1n];
 for(let j=1;j<=7*capN;j++){
  B100.push(B100[j-1]*100n);B101.push(B101[j-1]*101n);
  if(j<=capN){P27.push(P27[j-1]*27n);P16.push(P16[j-1]*16n);}
 }
 for(const e of [1,-1]){
  let primitive=0,withSixty=0,withExact=0;
  for(let n=e===1?260:56;n<=capN;n++){
   let maxD=54;
   for(let d=56;100*d<=27*n+2900;d+=2){
    if(P27[(d-2)/2]*B100[7*n]<=1024n*P16[(d-2)/2]*B101[7*n])maxD=d;
    else break;
   }
   if(maxD<56)continue;
   for(let s=1;s<=n/2;s++)for(let t=s;t<=n/2;t++){
    if(e===-1&&2*(s+t)>=n)break;
    if(gcd(gcd(n,s),t)!==1)continue;
    primitive++;
    const outside=ten(n,s,t,e).reduce((a,b)=>a+b,0);
    if(outside+60<n-maxD)continue;
    withSixty++;
    const E=exceptional(n,s,t,e);
    assert(E<=(e===1?40:60));
    if(E+outside<n-maxD)continue;
    withExact++;
   }
  }
  const got=[primitive,withSixty,withExact];
  assert.deepEqual(got,e===1?[8908829,410,0]:[4708172,16382,0]);
  console.log("Finite exclusion:",e,...got);
 }
}

// The notation in McKee--Smyth Table 2 uses the sign of
// (z^k + z^d - 1), which is the negative of the reciprocity sign.
const MS_TABLE2=[[25,11,1,1],[22,13,1,-1],[12,5,2,1],[20,7,2,1],[14,11,2,-1],[14,4,3,1],[19,5,3,1],[18,7,3,-1],[11,10,3,-1],[13,7,4,-1],[13,6,5,-1],[11,7,5,-1],[10,7,6,-1],[23,10,1,1],[20,12,1,-1],[13,10,2,-1],[13,6,4,-1],[20,9,1,1],[29,10,1,-1],[19,11,1,-1],[11,10,2,-1],[17,4,3,1],[23,5,3,-1],[10,8,3,-1],[11,6,4,-1],[21,9,1,1],[18,11,1,-1],[14,5,2,1],[19,7,2,-1],[12,9,2,-1],[9,7,4,-1],[18,8,1,1],[26,9,1,-1],[17,10,1,-1],[16,5,2,1],[10,9,2,-1],[24,4,3,1],[15,5,3,-1],[11,5,4,-1],[9,6,4,-1],[8,6,5,-1],[19,8,1,1],[16,10,1,-1],[11,8,2,-1],[31,4,3,1],[15,7,1,1],[28,8,1,1],[21,5,2,1],[19,4,3,-1],[12,5,3,-1],[8,7,3,-1],[7,6,5,-1],[33,8,1,-1],[16,9,1,-1],[23,5,2,1],[30,5,2,1],[16,7,1,1],[23,8,1,-1],[15,9,1,-1],[37,5,2,1],[9,8,2,-1],[29,5,2,-1],[12,6,1,1],[17,7,1,1],[14,9,1,-1],[22,5,2,-1],[10,7,2,-1],[15,4,3,-1],[7,6,4,-1],[13,6,1,1],[24,7,1,1],[25,7,1,1],[15,5,2,-1],[33,7,1,1],[12,4,3,-1],[29,7,1,-1],[14,8,1,-1],[21,7,1,-1],[14,6,1,1],[20,7,1,-1],[13,8,1,-1],[13,5,2,-1],[8,7,2,-1],[7,5,4,-1],[15,6,1,1],[12,8,1,-1],[9,6,2,-1],[20,6,1,1],[13,7,1,-1],[10,5,2,-1],[9,4,3,-1],[7,5,3,-1],[6,5,4,-1],[21,6,1,1],[22,6,1,1],[28,6,1,1],[29,6,1,1],[35,6,1,1],[36,6,1,1],[43,6,1,1],[50,6,1,1],[61,6,1,-1],[39,6,1,-1],[32,6,1,-1],[25,6,1,-1],[12,7,1,-1],[24,6,1,-1],[18,6,1,-1],[17,6,1,-1],[11,7,1,-1],[7,6,2,-1],[8,4,3,-1],[16,6,1,-1],[10,7,1,-1],[8,5,2,-1],[11,6,1,-1],[10,6,1,-1],[9,6,1,-1],[6,5,2,-1],[8,6,1,-1],[7,4,2,-1],[5,4,3,-1],[5,4,2,-1],[4,4,3,-1],[5,2,2,-1],[3,2,2,-1]];
const L=[1,1,0,-1,-1,-1,-1,-1,0,1,1];
function atRational(A,b=1177n,c=1000n){
 const n=A.length-1;
 return A.reduce((s,a,i)=>s+BigInt(a)*b**BigInt(i)*c**BigInt(n-i),0n);
}
function spectrumMinimum(){
 assert(atRational(L)>0n,"Lehmer exceeds right bracket");
 const polys=new Set();
 const accept=(f,mustBeNew)=>{
  assert(f.at(-1)===1&&f.reduce((a,b)=>a+Math.abs(b),0)===6);
  const str=f.join(",");
  if(mustBeNew)assert(!polys.has(str));
  polys.add(str);
  if(split(f,L))return 1;
  assert(atRational(f)<0n, f);
  return 0;
 };
 let sporadic=0,starts=0;
 assert.equal(MS_TABLE2.length,126);
 for(const [n,k,d,e]of MS_TABLE2){
  const f=new Array(n+k+1).fill(0);
  for(const [i,c]of [[n+k,1],[n+k-d,-1],[n,-1],[k,e],[d,e],[0,-e]])f[i]+=c;
  sporadic+=accept(f,true);
 }
 for(const [k,j,plus,minus]of [[1,0,3,4],[2,1,2,5],[3,1,1,8],[3,2,1,6],[4,3,1,7],[5,4,1,8]]){
  const p=new Array(k+1).fill(0);p[k]=1;p[j]--;p[0]--;
  assert(atRational(p)<0n);
  for(const [n,e]of [[plus,1],[minus,-1]]){
   const f=new Array(n+k+1).fill(0);
   for(let i=0;i<=k;i++){
    f[n+i]+=p[i];f[k-i]+=e*p[i];
   }
   starts+=accept(f,false);
  }
 }
 assert.deepEqual([sporadic,starts,polys.size],[13,2,136]);
 console.log("Minimum checked against published exact data:",sporadic,"sporadic and",starts,"family entries");
}
smallControl();
proofRange();
spectrumMinimum();
console.log("PASS");
