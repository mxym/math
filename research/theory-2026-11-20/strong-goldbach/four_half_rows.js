'use strict';
// Row-first census. Node.js; exact small integer determinants.
const {createHash}=require('node:crypto');
function det(A){let n=A.length;if(!n)return 1;if(n===1)return A[0][0];let B=A.map(x=>x.slice()),s=1,d=1;for(let i=0;i<n-1;i++){let k=i;while(k<n&&!B[k][i])k++;if(k===n)return 0;if(k!==i){[B[k],B[i]]=[B[i],B[k]];s=-s;}for(let j=i+1;j<n;j++)for(let t=i+1;t<n;t++)B[j][t]=(B[j][t]*B[i][i]-B[j][i]*B[i][t])/d;d=B[i][i];}return s*B[n-1][n-1];} 
function vdot(a,b){return a.reduce((x,t,j)=>x+t*b[j],0);}
function sum(a){return a.reduce((x,y)=>x+y,0);}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);return b?gcd(b,a%b):a;}
function primitive(a){let d=a.reduce(gcd,0);return d?a.map(x=>x/d):a;}
function opts(n,i){let out=[];for(let a=0;a<=n;a++)for(let b=0;b<=n-a;b++)for(let c=0;c<=n-a-b;c++)for(let d=0;d<=n-a-b-c;d++){let r=[a,b,c,d];if(i>=2&&r[i-2])continue;if(i===1&&sum(r)!==n||i===0&&!sum(r))continue;out.push(r)}return out;}
function checkG(R){let A=R.map((r,i)=>r.map((x,j)=>x-(i===j+2)));let D=Array.from({length:6},()=>Array(6).fill(0));for(let i=0;i<6;i++)for(let j=i+1;j<6;j++){let v=det(A.filter((_,t)=>t!==i&&t!==j))*(-1)**(i+j);D[i][j]=v;D[j][i]=-v;}
if(D[0][1]===0)return null;for(let i=0;i<6;i++){let h=D[i];if(h.filter(x=>x!==0).length<4||h.filter(x=>x>0).length<2||h.filter(x=>x<0).length<2)return null;}
let L=primitive(R.map((_,i)=>det(R.filter((_,j)=>j!==i).map(r=>[...r,1]))*(-1)**i));if(!L[2]||!L.some(x=>x>0)||!L.some(x=>x<0))return null;return [L,D];}
function enumerate(n=2){let out=[],raw=[];let C=Array.from({length:6},(_,i)=>opts(n,i));let hist=[];function dfs(R,S){let i=R.length;if(i===6){raw.push(R.flat().join(""));let t=checkG(R);if(t)out.push([R,...t]);return;}for(const r of C[i]){if(R.some(x=>x.toString()===r.toString()))continue;let s=S.slice(),ok=true;for(let j=0;j<4;j++)if(r[j]&&(i<2||i>j+2)){if(s[j]){ok=false;break;}s[j]=true;}if(ok)dfs([...R,r],s);}}dfs([],Array(4).fill(false));return [raw,out];}
const [raw,first]=enumerate();
const eq=first.filter(([R,l,D])=>D.every(h=>vdot(h,[2,2,1,1,1,1])===0));
const positive=eq.filter(([R,l,D])=>{let a=0,pos=false,neg=false;for(let j of [2,3,4,5,1,0]){a+=l[j];if(a>0)pos=true;if(a<0)neg=true;}return pos&&neg;});
const code=x=>x[0].flat().join('');
const hash=x=>createHash('sha256').update(x.slice().sort().join('\n')+'\n').digest('hex');
for(const [name,items] of [['raw',raw],['rank-gale',first.map(code)],['equal',eq.map(code)],['terminal',positive.map(code)]])console.log(name,items.length,hash(items));
console.log('terminal codes and primitive null rows (up to sign):');
for(let item of positive)console.log(code(item),item[1].join(' '));
if(raw.length!==16609||first.length!==902||eq.length!==20||positive.length!==4)throw new Error('census mismatch');
