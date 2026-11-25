'use strict';
const check=(v,msg)=>{if(!v)throw Error(msg)};
const equal=(x,y)=>JSON.stringify(x)===JSON.stringify(y);
function times(a,b){
 let c=0;for(let i=0;i<2;i++)for(let j=0;j<2;j++)for(let k=0;k<2;k++)
 c^=(((a>>(2*i+k))&(b>>(2*k+j))&1)<<(2*i+j));
 return c;
}
const tr=a=>(a^(a>>3))&1;
const gl=Array.from({length:16},(_,k)=>k).filter(k=>(((k&1)*(k>>3&1))^((k>>1&1)*(k>>2&1)))===1);
const plane=(a,b)=>[a,b,a^b].sort((x,y)=>x-y).slice(0,2);
const key=([a,b])=>16*a+b;
const orbit=new Map();
for(let a=1;a<16;a++)for(let b=a+1;b<16;b++){
 if(key(plane(a,b))!==key([a,b]))continue;
 const rep=Math.min(...gl.map(g=>{
   const gi=gl.find(h=>times(g,h)===9);
   return key(plane(times(times(g,a),gi),times(times(g,b),gi)));
 }));
 if(!orbit.has(rep))orbit.set(rep,[]);
 orbit.get(rep).push([a,b]);
}
const expected=[[1,2,3],[1,4,3],[1,6,6],[1,8,3],[1,10,6],[1,14,6],[2,4,3],[2,9,3],[6,11,1],[7,9,1]];
const got=[...orbit].sort((x,y)=>x[0]-y[0]).map(([k,ls])=>[k>>4,k&15,ls.length]);
check(equal(got,expected),'conjugation orbit census');
function f2rank(a,b,s) {
 const n=1<<s,A=[a,b],B=[];
 for(let x=0;x<n;x++){
  let row=0n;
  for(let y=0;y<n;y++){
   let z=9;
   for(let j=0;j<s&&z;j++)z=times(times(z,A[x>>j&1]),A[y>>j&1]);
   if(tr(z))row|=1n<<BigInt(y);
  }
  for(let j=0;j<n&&row;j++)if((row>>BigInt(j))&1n){
   if(B[j])row^=B[j];else{B[j]=row;break;}
  }
 }
 return B.filter(Boolean).length;
}
function c(s) {
 let n=0;for(let x=0;x<(1<<s);x++){
 if(!Array.from({length:s},(_,j)=> (x>>j&1)&&!(x>>((j+1)%s)&1)&&(x>>((j+2)%s)&1)).some(Boolean))n++;
 }return n;
}
for(let s=2;s<=8;s++){
 const ranks=expected.map(([a,b])=>f2rank(a,b,s));
 check(equal(ranks,[1,1,2**(s-1),2,2,c(s),2,0,2,2]),'F2 ranks '+s);
 for(const [rep,ls] of orbit)for(const [a,b] of ls)
  check(f2rank(a,b,s)===ranks[expected.findIndex(([x,y])=>key([x,y])===rep)],'F2 individual plane');
 console.log('F2',s,Math.max(...ranks),ranks.join(','));
}
const m4=(x,y)=>{let z=((y&1)?x:0)^((y&2)?x<<1:0);if(z&4)z^=7;return z;};
const pred=(a,b,c0,d,s)=>{
 const Q=m4(b,c0),P=m4(a,d);
 if(!Q)return Number(!!a)+Number(!!d);
 if(!a&&!d)return 2;
 if(!a||!d)return c(s);
 return P===Q?1:3*2**(s-2);
};
function f4rank(K,s){
 const n=1<<s;
 const M=Array.from({length:n},(_,a)=>Uint8Array.from({length:n},(_,b)=>{
  let z=1;for(let j=0;j<s&&z;j++)z=m4(m4(z,K[a>>j&1][b>>j&1]),K[b>>j&1][a>>((j+1)%s)&1]);return z;
 }));
 let r=0;
 for(let j=0;j<n;j++){
  let i=r;while(i<n&&!M[i][j])i++;if(i===n)continue;
  [M[r],M[i]]=[M[i],M[r]];const inv=m4(M[r][j],M[r][j]);
  for(let i=r+1;i<n;i++)if(M[i][j]){
   const x=m4(M[i][j],inv);for(let k=j;k<n;k++)M[i][k]^=m4(x,M[r][k]);
  }r++;
 }return r;
}
for(let s=2;s<=6;s++){
 let max=0;
 for(let a=0;a<4;a++)for(let b=0;b<4;b++)for(let c=0;c<4;c++)for(let d=0;d<4;d++){
  const r=f4rank([[a,b],[c,d]],s);max=Math.max(max,r);
  check(r===pred(a,b,c,d,s),'F4 stratum '+[a,b,c,d,s]);
 }
 console.log('F4',s,max);
}
