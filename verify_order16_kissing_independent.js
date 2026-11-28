'use strict';
const n=16,sz=1<<n,pop=new Uint8Array(sz);for(let i=1;i<sz;i++)pop[i]=pop[i&(i-1)]+1;
const C=Array.from({length:33},(_,i)=>[1]);for(let i=1;i<33;i++)for(let j=1;j<=i;j++)C[i][j]=(C[i-1][j-1]||0)+(C[i-1][j]||0);
const ch=(i,j)=>j>=0&&(i>=0&&j<=i)?C[i][j]:0,ceil=(a,b)=>Math.ceil(a/b);
function colex(r){const colors=new Uint32Array(sz),ok=new Uint8Array(sz),idx=new Int32Array(sz),v=Array.from({length:r+1},()=>[0]);ok[0]=1;
 for(let m=1;m<sz;m++){const b=m&-m,p=m^b,i=31-Math.clz32(b),c=1<<(i%r);if(ok[p]&&!(colors[p]&c)){ok[m]=1;colors[m]=colors[p]|c;idx[m]=v[pop[m]].length;v[pop[m]].push(m);}}
 const bound=v.map(a=>new Int32Array(a.length));for(let j=1;j<r;j++){for(let t=1;t<v[j+1].length;t++){let m=v[j+1][t];bound[j][idx[m^(m&-m)]]++;}for(let t=1;t<bound[j].length;t++)bound[j][t]+=bound[j][t-1];}
 return bound;
}
function floorProfile(r){let q=n-r,m0=ch(r,2),table=Array(121).fill(null);function fill(k,left,D){
 if(k<r){for(let t=0;t<=left;t++){for(let j=0;j<t;j++)D.push(k);fill(k+1,left-t,D);D.length-=t;}return;}
 if(left)return;
 let m=m0+D.reduce((a,b)=>a+b,0),cc=Array.from({length:r+1},(_,j)=>ch(r,j)+D.reduce((s,d)=>s+ch(d,j-1),0)),ls=[];for(let i=0;i<q;i++)for(let j=0;j<i;j++)ls.push(Math.max(0,D[i]+D[j]-r));ls.sort((a,b)=>a-b);
 for(let e=0;e<=ls.length;e++){let M=m+e,w=table[M]||(table[M]=Array(r+1).fill(Infinity));for(let j=3;j<=r;j++){
 let z=cc[j];if(j===3){let out=q?Math.max(0,ceil(4*e*e-q*q*e,3*q)):0;z=Math.max(z+out,ceil(4*M*M-n*n*M,3*n));}w[j]=Math.min(w[j],z);}
 if(e<ls.length)for(let j=3;j<=r;j++)cc[j]+=ch(ls[e],j-2);}
 }fill(0,q,[]);return table;}
function walk(r){const U=colex(r),L=floorProfile(r),hits=new Map();
 for(let m=ch(r,2);m<=U[1][n];m++){let old=Array.from({length:3},()=>new Map),raw=new Set;old[+(m<n)].set(m,n);
 for(let k=2;k<r;k++){const seg=[[],[],[]];function put(i,j,a,b){if(i<=j)seg[b].push([a,i,j]);}
 for(let b=0;b<3;b++)for(let[a,c]of old[b]){let lo=Math.max(L[m][k+1],ceil(k*k*a*a-n*a*c,(k*k-1)*c)),hi=U[k][a];if(lo>hi)continue;
 if(b===2)put(lo,hi,a,2);else if(b===0){put(lo,Math.min(hi,a-1),a,1);put(Math.max(lo,a),hi,a,0);}else{put(lo,Math.min(hi,a),a,1);put(Math.max(lo,a+1),hi,a,2);if(hi>a)raw.add(k+','+a);}}
 old=seg.map(ss=>{let z=new Map;if(!ss.length)return z;ss.sort((a,b)=>b[0]-a[0]);let max=ss.reduce((b,t)=>Math.max(b,t[2]),0),p=Int32Array.from({length:max+2},(_,i)=>i);
 function nxt(x){let j=x;while(p[j]!==j)j=p[j];while(p[x]!==x){let y=p[x];p[x]=j;x=y;}return j;}
 for(let [a,i,j]of ss)for(let x=nxt(i);x<=j;x=nxt(x)){z.set(x,a);p[x]=nxt(x+1);}return z;});}
 if(old[2].size)for(let h of raw){let[k,a]=h.split(',').map(Number);hits.set(k,Math.min(hits.get(k)||Infinity,a));}}
 return [...hits].sort((a,b)=>a[0]-b[0]);}
for(let r=3;r<=16;r++)console.log(r,JSON.stringify(walk(r)));
function scores(n,r,cs){let f=[1],num=0,best=-Infinity,ix;
 function go(a,left,p){if(!left){num++;let z=cs.reduce((d,[i,w])=>d+w*(f[i]||0),0);if(z>best){best=z;ix=p.slice();}return;}if(p.length>=r)return;
 for(let u=a;u<=left;u++){let old=f;f=Array.from({length:old.length+1},(_,j)=>(old[j]||0)+u*(old[j-1]||0));p.push(u);go(u,left-u,p);p.pop();f=old;}}
 go(1,n,[]);return [num,best,ix];}
for(let [n,r,cs]of [[16,8,[[3,7168],[4,-2968],[5,663]]],[7,7,[[2,1],[3,1],[4,-1]]],[16,11,[[4,379],[5,-236],[6,62]]]]) console.log('linear maximum',n,r,...scores(n,r,cs));
function witness(n,r){let A=Array(n).fill(0),edge=(i,j)=>{A[i]|=1<<j;A[j]|=1<<i;},k=r===5?6:r;for(let j=0;j<k;j++)for(let i=0;i<j;i++)if(r!==5||i||j!==1)edge(i,j);
 if(r===7||r===8){for(let i=k;i<k+4;i++)for(let j=k+4;j<n;j++)edge(i,j);for(let i=k;i<n;i++){if(r===7&&i===k){for(let h=1;h<7;h++)edge(i,h);}else if(r===7){edge(i,i<k+4?1:0);}else edge(i,i<k+4?0:1);}}
 let m=(1<<n)-1,F=Array(n+1).fill(0),cl=new Uint8Array(m+1);cl[0]=1;F[0]=1;for(let S=1;S<=m;S++){let b=S&-S,p=S^b;if(cl[p]&&(p&~A[31-Math.clz32(b)])===0){cl[S]=1;let t=S,c=0;while(t){t&=t-1;c++;}F[c]++;}}while(!F.at(-1))F.pop();
 let conn=1,prev=0;while(conn!==prev){prev=conn;for(let i=0;i<n;i++)if(prev>>i&1)conn|=m&~(A[i]|1<<i);}
 console.log('witness',n,r,F.join(),conn===m);if(conn!==m||F.length!==r+1)throw Error('witness');}
for(let a of [[16,5],[16,6],[16,7],[17,8]])witness(...a);
