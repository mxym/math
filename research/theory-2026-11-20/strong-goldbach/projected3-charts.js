'use strict';
const M=Number(process.argv[2]||3);
if(![3,4].includes(M))throw Error("implemented bounds 3,4");
const mode=process.argv[3]||'v',rows=[],R=[],K=[],pop=(i)=>i?1+pop(i&(i-1)):0;
for(let total=2;total<=M;total++){let r=[];function comp(i,m){if(i===4){rows.push([...r,m]);return;}for(let n=0;n<=m;n++){r[i]=n;comp(i+1,m-n)}}comp(0,total);}
for(let i=0;i<6;i++){R[i]=rows.filter(r=>!i||!r[i-1]);K[i]=R[i].map(r=>r.map((x,j)=>x-(i===j+1)));}
const picks={};
function setup(n){let ks=[];for(let h=0;h<=n;h++){let masks=[];for(let m=0;m<1<<n;m++)if(pop(m)===h)masks.push(m);ks.push(masks);}
let ops=[[]];for(let h=1;h<=n;h++)ops[h]=ks[h].map(m=>{let u=[];for(let j=0;j<n;j++)if(m>>j&1)u.push([ks[h-1].indexOf(m^(1<<j)),j,pop(m>>(j+1))%2?-1:1]);return u;});return ops;}
for(let n of [5,6])picks[n]=setup(n);
function extend(a,b,k){return picks[b.length][k].map(ops=>{let z=0;for(let [ix,j,sg] of ops)z+=sg*a[ix]*b[j];return z;});}
function cross(a){let v=a.slice().reverse().map((x,i)=>i%2?-x:x);let g=0;for(let x of v)g=gcd(g,Math.abs(x));return g?v.map(x=>x/g):null;}
function gcd(a,b){while(b){let c=a%b;a=b;b=c;}return a;}
function dot(a,b){let z=0;for(let i=0;i<a.length;i++)z+=a[i]*b[i];return z;}
function srt(a){return a.slice().sort((a,b)=>a-b);}
function oriented(v){let a=srt(v),b=a.slice().reverse().map(x=>-x);for(let i=0;i<a.length;i++)if(a[i]!==b[i])return a[i]<b[i]?1:-1;return 1;}
let count=0,formed=0,vg=0,ng=0,answers=new Set();
function recOpts(opts,act){let A=[];function go(i){if(i===6){act(A);return;}for(let r of opts[i]){A[i]=r;go(i+1);}}go(0);}
function canonical(A,v){let us=[];for(let s of [1,-1]){let ix=[0,1,2,3,4].sort((a,b)=>s*(v[a]-v[b]));let vr=ix.map(i=>s*v[i]);let ar=[-1,...ix].map(i=>ix.map(j=>A[i+1][j]).join(''));us.push({vr,key:[...ar,...vr].join(' ')});}for(let j=0;j<5;j++)if(us[0].vr[j]!==us[1].vr[j])return us[0].vr[j]<us[1].vr[j]?us[0].key:us[1].key;
return us[0].key<us[1].key?us[0].key:us[1].key;}
function single(A){return [0,1,2,3,4].some(j=>A.filter(r=>r[j]).length===1);}
function eig(v){let a=srt(v);return a[1]<0&&a[3]>0&&!a.includes(0)&&new Set(a).size===5;}
if(mode==='v'){let V=new Set();function go(i,h){if(i===4){let v=cross(h);if(!v||!eig(v))return;v=srt(v.map(x=>x*oriented(v)));V.add(v.join(','));return;}for(let r of K[i])go(i+1,extend(h,r,i+1));}go(0,[1]);
for(let key of V){let v=key.split(',').map(Number),opts=R.map((rows,i)=>rows.filter(r=>dot(r,v)===(i?v[i-1]:0)));if(opts.some(o=>!o.length))continue;vg++;recOpts(opts,A=>{formed++;if(single(A)){count++;answers.add(canonical(A,v));}});}console.error("directions, feasible directions, raw charts, singleton charts",V.size,vg,formed,count);}
else if(mode==='w'){/* Enumerate unordered five independent projected row equations first, without imposing an index gauge. */
let P=rows.map(r=>[...r,-1]),W=new Set();function go(j,i,h){if(i===5){let w=cross(h);if(!w||!w[5])return;if(w[5]<0)w=w.map(x=>-x);if(w.slice(0,5).some(k=>k<=0||k>=w[5])||w.slice(0,5).filter(k=>2*k<=w[5]).length<3)return;
W.add([...srt(w.slice(0,5)),w[5]].join(','));return;}
for(let k=j;k<=P.length-(5-i);k++){let hh=extend(h,P[k],i+1);if(hh.some(x=>x))go(k+1,i+1,hh);}}go(0,0,[1]);
/* Use all 6 rows of B' as needed: cumulative wedge basis stops at rank 4,
   then all remaining rows must annihilate the same vector. */
for(let key of W){let ww=key.split(',').map(Number),w=ww.slice(0,5),opts=R.map(rr=>rr.filter(r=>dot(r,w)===ww[5]));if(opts.some(o=>!o.length))continue;ng++;
let A=[];function dfs(i,rank,h,v){if(i===6){if(v&&single(A))answers.add(canonical(A,v));return;}for(let r of opts[i]){A[i]=r;let b=r.map((t,j)=>t-(i===j+1));if(v){if(!dot(b,v))dfs(i+1,rank,h,v);continue;}let hh=extend(h,b,rank+1);if(!hh.some(x=>x)){dfs(i+1,rank,h,null);continue;}if(rank+1===4){let vv=cross(hh);if(eig(vv))dfs(i+1,4,hh,vv);}else dfs(i+1,rank+1,hh,null);}}dfs(0,0,[1],null);}console.error("weight vectors, row-feasible weights, canonical signatures",W.size,ng,answers.size);}
else throw Error("unknown method");for(let s of [...answers].sort())console.log(s);

