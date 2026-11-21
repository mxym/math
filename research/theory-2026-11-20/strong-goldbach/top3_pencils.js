function det(A){let n=A.length;if(!n)return 1;if(n===1)return A[0][0];let B=A.map(x=>x.slice()),s=1,d=1;for(let i=0;i<n-1;i++){let k=i;while(k<n&&!B[k][i])k++;if(k===n)return 0;if(k!==i){[B[k],B[i]]=[B[i],B[k]];s=-s;}for(let j=i+1;j<n;j++)for(let t=i+1;t<n;t++)B[j][t]=(B[j][t]*B[i][i]-B[j][i]*B[i][t])/d;d=B[i][i];}return s*B[n-1][n-1];} 
function vdot(a,b){return a.reduce((x,t,j)=>x+t*b[j],0);}
function sum(a){return a.reduce((x,y)=>x+y,0);}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);return b?gcd(b,a%b):a;}
function primitive(a){let d=a.reduce(gcd,0);return d?a.map(x=>x/d):a;}

function options(){let O=[];for(let i=0;i<6;i++){let s=[];for(let a=0;a<=2;a++)for(let b=0;b<=2-a;b++)for(let c=0;c<=2-a-b;c++){let t=[a,b,c];if(i>=2&&i<=4&&t[i-2])continue;s.push(t)}O.push(s)}return O}
function gamma(A){let D=Array.from({length:6},()=>Array(6).fill(0));for(let i=0;i<6;i++)for(let j=i+1;j<6;j++){let v=det(A.filter((_,t)=>t!==i&&t!==j))*(-1)**(i+j);D[i][j]=v;D[j][i]=-v;}return D}
function okgal(D){return D[0][1]&&D.every(h=>h.filter(x=>x>0).length>=2&&h.filter(x=>x<0).length>=2);}

function charts(){let O=options(),out=[];function run(Z,smaller){let i=Z.length;if(i===6){out.push(Z);return;}for(let r of O[i]){let bits=0;for(let j=0;j<3;j++)if(r[j]&&(i<2||i>j+2))bits|=1<<j;if(bits&smaller)continue;run([...Z,r],smaller|bits);}}run([],0);return out;}
function cw(C){return primitive(C.map((_,i)=>det(C.filter((_,j)=>j!==i))*(-1)**i));}
function getSZ(Z,k=1000){const dcap=Z.map(r=>2-sum(r));if(dcap[0]===2&&dcap[1]>0)return;const F=Z.map((r,i)=>r.map((x,j)=>x-(i===j+2))),v=[2,2,1,1,1,2],e=[0,0,0,0,0,1];
let A=gamma(F.map((r,i)=>[...r,v[i]])),B=gamma(F.map((r,i)=>[...r,-e[i]]));
let root=0;for(let i=0;i<6;i++)for(let j=0;j<6;j++)if(A[i][j])root=Math.max(root,Math.abs(B[i][j]/A[i][j]));
let G=A.map((r,i)=>r.map((x,j)=>x*Math.round(12*k)+12*B[i][j]));
let J=cw(F.map((r,i)=>[...r,v[i],e[i]]));
if(J.every(x=>!x)){let k;for(let i=0;i<6;i++)for(let j=0;j<6;j++)if(A[i][j])k=-B[i][j]/A[i][j];return {Z,J,root,dependent:k??null};}
if(!okgal(G))return;
let tmps=[];for(let h of B){if(!vdot(h,v))continue;let H=primitive(h),t=vdot(H,v);if(t<0){H=H.map(x=>-x);t=-t;}
let lo=H[1]*dcap[1],hi=lo;for(let i of [0,2,3,4]){if(i===0&&dcap[1])continue;lo+=Math.min(0,H[i]*dcap[i]);hi+=Math.max(0,H[i]*dcap[i]);}tmps.push([H,t,lo,hi]);}
tmps.sort((x,y)=>(x[3]-x[2])/x[1]-(y[3]-y[2])/y[1]);let [psi,pv,lo,hi]=tmps[0];
let cand=[];for(let h of A){if(!h[5])continue;let H=primitive(h);if(H[5]<0)H=H.map(x=>-x);let d=H[5],Tmin=Math.ceil(d*(pv-hi)/pv),Tmax=Math.floor(d*(pv-lo)/pv);cand.push([H,Tmin,Tmax]);}cand.sort((x,y)=>(x[2]-x[1])-(y[2]-y[1]));let [phi,L,H]=cand[0];return {Z,J,psi,pv,phi,L,H,root};}

function getsets(C,lo=100,hi=null,at=false){let S=[];let xs=['d0','d1','d2','d3','d4','d5'];
function lin(v){return '('+(v.map((x,i)=>x?x+'*'+xs[i]:null).filter(Boolean).join(' + ')||'0')+')';}
function union(s){return '('+s.join(' or ')+')'}
for(let obj of C){let {Z,J,psi,pv,phi,L,H}=obj,z=Z.map(r=>2-sum(r)),v=phi[5];let left=Array.from({length:6},(_,i)=>Array.from({length:6},(_,s)=>{let A=Z.map((r,j)=>[...r,+(j===s),1]).filter((_,j)=>j!==i);return det(A)*(-1)**i;}));let prefix=[],w=Array(6).fill(0);for(let i of [2,3,4,5,1]){w=w.map((x,j)=>x+left[i][j]);prefix.push(lin(w));}
let allowed=true,common=[lin(J)+'=0','d5=0',union([lin(left[2])+'<0',lin(left[2])+' >0']),union(prefix.map(x=>x+'<0')),union(prefix.map(x=>x+'>0'))];
common.push(union([prefix[0]+'<0',prefix[1]+'<0',prefix[2]+'<=0']),union([prefix[0]+'>0',prefix[1]+'>0',prefix[2]+'>=0']));
for(let i=0;i<6;i++)for(let j=0;j<i;j++){if(Z[i].join()===Z[j].join())common.push(union([xs[i]+'<'+xs[j],xs[i]+'>'+xs[j]]));
let com=sum(Z[i].map((x,t)=>Math.min(x,Z[j][t])));if(com>=2)allowed=false;if(com===1)common.push(union([xs[i]+'=0',xs[j]+'=0']));}
if(!allowed)continue;
if(z[1]>0)common.push('d0=0');if(z[0]===2)common.push('d0>=1');
for(let t=L;t<=H;t++){let u=pv*(v-t);if(!u)continue;let g=gcd(v,u),P=v/g*Math.sign(u),Q=Math.abs(u)/g;let cc=[...common,lin(phi)+'='+t,'j='+P+'*'+lin(psi),at?'12*j='+Math.round(lo*12)*Q:'12*j>'+Math.round(lo*12)*Q,Q+'*d1='+z[1]+'*j'];
if(!at&&hi!==null)cc.push('12*j<'+Math.round(hi*12)*Q);for(let i=0;i<6;i++)cc.push(xs[i]+'>=0',Q+'*'+xs[i]+'<='+z[i]+'*j');
for(let i=0;i<6;i++)for(let j=0;j<i;j++){if(Z[i].some((x,t)=>x&&Z[j][t]))continue;cc.push(union([Q+'*'+xs[i]+'<=j',Q+'*'+xs[j]+'<=j']));}
let ss='{ [j,'+xs.join(',')+'] : '+cc.join(' and ')+' }';
S.push({id:Z.flat().join('')+'/'+t+'/'+Q,P,Q,t,ss});}}return S;}
function makeAll(){let cuts=[1,4/3,3/2,2,3],Z=charts(),R=[];for(let i=0;i<cuts.length;i++){let lo=cuts[i],hi=cuts[i+1]??null,mid=hi?(lo+hi)/2:100;for(let at of (i===0?[false]:[true,false])){let C=Z.map(z=>getSZ(z,at?lo:mid)).filter(x=>x&&x.psi),S=getsets(C,lo,hi,at);for(let s of S){s.rail=i+':'+(at?1:0);R.push(s);}}}return R;}
function controls(){let Z=charts(),roots=new Set(),dep=0;for(let E of Z){let F=E.map((r,i)=>r.map((x,j)=>x-(i===j+2))),v=[2,2,1,1,1,2];let A=gamma(F.map((r,i)=>[...r,v[i]])),B=gamma(F.map((r,i)=>[...r,-(i===5)]));let N,D=0,rankE=false;for(let i=0;i<6;i++)for(let j=i+1;j<6;j++){let x=A[i][j],y=B[i][j];if(y)rankE=true;if(x){N=-y;D=x;if(N/D>1){let g=gcd(x,y);roots.add(Math.abs(y/g)+'/'+Math.abs(x/g));}}}
if(!rankE)continue;let J=cw(F.map((r,i)=>[...r,v[i],+(i===5)]));if(!J.some(Boolean)){dep++;if(D&&N/D>1&&A.every((r,i)=>r.every((x,j)=>N*x+D*B[i][j]===0)))throw Error('unhandled dependent k>1');}}
if(Z.length!==7290||[...roots].sort().join()!==['4/3','3/2','2/1','3/1'].sort().join())throw Error('pencil critical value mismatch');}
controls();for(let r of makeAll())console.log(JSON.stringify(r));
