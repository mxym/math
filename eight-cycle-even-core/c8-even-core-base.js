
const p=1009,mod=x=>(x%p+p)%p;
const inv=x=>{for(let j=1;j<p;j++)if(mod(j*x)==1)return j;throw Error(x)}
const G={0:[4,5,2,8],1:[3,7,13,11]},cs=[0,0,2,3,7,11,17,29,67];
const mul=(a,b)=>[a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]].map(mod);
const neg=k=>k<2?k:(k^1);
function ev(a,b){let s=[];for(let i=0;i<4;i++)s.push(a[i],neg(b[i]));
let first=s.findIndex(k=>k<2);if(first<0)throw Error('nocore');
let m=[1,0,0,1];
for(let j=0;j<8;j++){let i=(first+j)%8,k=s[i];if(k<2)m=mul(m,G[k]);else{if(j==7||s[(i+1)%8]!=neg(k))return 0;m=mul(m,[cs[neg(k)],0,0,0]);j++}}
return mod(m[0]+m[3]);}
function words(L){let out=[];for(let i=0;i<9;i++)for(let j=0;j<9;j++)for(let k=0;k<9;k++)for(let l=0;l<9;l++){let a=[i,j,k,l];if(a.filter(x=>x>=2).sort().join(',')==L.join(','))out.push(a)}return out;}
function R(M){let a=M.map(x=>x.slice()),k=0;for(let j=0;j<a[0].length;j++){let i=a.findIndex((r,i)=>i>=k&&r[j]);if(i<0)continue;[a[k],a[i]]=[a[i],a[k]];let iv=inv(a[k][j]);a[k]=a[k].map(x=>mod(x*iv));for(let l=k+1;l<a.length;l++){let f=a[l][j];if(f)a[l]=a[l].map((x,n)=>mod(x-f*a[k][n]));}k++;}return k;}
function sectors(W,M){let S=[];for(let z of [1,1008,469,540]){let seen=new Set(),Q=[];for(let i=0;i<W.length;i++){if(seen.has(i))continue;let a=W[i],j=i,b=[],c=1;
do{seen.add(j);b.push([j,c]);a=a.slice(1).concat(a[0]);j=W.findIndex(x=>x.join(',')==a.join(','));c=mod(c*z)}while(j!=i);if(c==1)Q.push(b);}
S.push(Q.length?[Q.length,R(Q.map(row=>Q.map(col=>mod(col.reduce((s,[j,z])=>s+z*M[row[0][0]][j],0)))))]:[0,0]);}return S;}
const expected=[
[[],16,12,[[6,6],[4,2],[3,2],[3,2]]],
[[2],32,32,[[8,8],[8,8],[8,8],[8,8]]],
[[2,2],24,24,[[7,7],[7,7],[5,5],[5,5]]],
[[2,3],48,46,[[12,12],[12,10],[12,12],[12,12]]],
[[2,4],48,48,[[12,12],[12,12],[12,12],[12,12]]],
[[2,2,2],8,8,[[2,2],[2,2],[2,2],[2,2]]],
[[2,2,3],24,24,[[6,6],[6,6],[6,6],[6,6]]],
[[2,2,4],24,24,[[6,6],[6,6],[6,6],[6,6]]],
[[2,3,4],48,48,[[12,12],[12,12],[12,12],[12,12]]],
[[2,4,6],48,48,[[12,12],[12,12],[12,12],[12,12]]]
];
for(const item of expected){const L=item[0],W=words(L),M=W.map(a=>W.map(b=>ev(a,b)));const observed=JSON.stringify([L,W.length,R(M),sectors(W,M)]);if(observed!==JSON.stringify(item))throw Error('base certificate changed: '+observed);console.log(observed);}
