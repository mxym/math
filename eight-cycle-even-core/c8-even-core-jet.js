
const p=1009,mod=x=>(x%p+p)%p;
const inv=x=>{for(let j=1;j<p;j++)if(mod(j*x)==1)return j;throw Error(x)}
const rot=w=>w.slice(1).concat(w[0]);
const neg=k=>k<2?k:(k^1);
const G={0:[4,5,2,8],1:[3,7,13,11]},cs=[0,0,2,3,7,11,17,29,67]; let trial=0;
const of=(r,c,v)=>Array.from({length:r},()=>Array(c).fill(v||0))
const zero=a=>of(a.length,a[0]?.length||0);
function plus(a,b,k=1){return a.map((r,i)=>r.map((x,j)=>mod(x+k*b[i][j])))}
function mul(a,b){let c=of(a.length,b[0]?.length||0);for(let i=0;i<a.length;i++)for(let k=0;k<b.length;k++)if(a[i][k])for(let j=0;j<b[0].length;j++)c[i][j]+=a[i][k]*b[k][j];return c.map(r=>r.map(mod))}
function sub(a,ri,ci){return ri.map(i=>ci.map(j=>a[i][j]))}
function gauss(a){let M=a.map(r=>r.slice()),cols=[],rows=M.map((_,i)=>i),k=0;for(let j=0;j<M[0]?.length;j++){let i=M.findIndex((r,i)=>i>=k&&r[j]);if(i<0)continue;[M[k],M[i]]=[M[i],M[k]];[rows[k],rows[i]]=[rows[i],rows[k]];let iv=inv(M[k][j]);M[k]=M[k].map(x=>mod(x*iv));for(let l=0;l<M.length;l++)if(l!=k){let f=M[l][j];if(f)M[l]=M[l].map((x,n)=>mod(x-f*M[k][n]));}cols.push(j);k++;}return {rows:rows.slice(0,k),cols,M,k};}
const inverse=a=>gauss(a.map((r,i)=>r.concat(r.map((_,j)=>+(i==j))))).M.map(r=>r.slice(a.length))
function basis(q,z){let reps=[],idx=Array(q**4).fill(-1),wt=Array(q**4).fill(0),signed=[],abs=[],grp=new Map();
 const code=w=>w.reduce((a,x)=>a*q+x,0);const dec=i=>[i/q**3|0,(i/q**2|0)%q,(i/q|0)%q,i%q];
 let rep=new Set();
 for(let i=0;i<q**4;i++){if(rep.has(i))continue;let w=dec(i),v=w.slice(),orb=[],c=1;
 do{rep.add(code(v));orb.push([code(v),c]);v=rot(v);c=mod(c*z)}while(code(v)!=i);
 if(c!=1)continue;
 let key=w.filter(j=>j>=2).sort().join(',');
 if(!grp.has(key))grp.set(key,[]);
 grp.get(key).push(reps.length);
 signed.push(key);abs.push(w.filter(j=>j>=2).map(j=>j>>1).sort().join(','));
 for(let [k,u] of orb){idx[k]=reps.length;wt[k]=u;} reps.push(w);
 }
 return {reps,idx,wt,code,grp,signed,abs}
}
function jets(q,z,D,opt={}){let B=basis(q,z),{reps,idx,wt,code}=B,M=Array.from({length:D+1},()=>of(reps.length,reps.length));
 let A=of(q,0);const edge=(i,j,k,b,d)=>{if(b)A[i].push([j,k,b,d]);}
 for(let x=0;x<2;x++)for(let i=0;i<2;i++)for(let j=0;j<2;j++)edge(i,j,x,G[x][2*i+j],0)
 for(let i=2;i<q;i++){edge(0,i,i,1,0);edge(i,0,neg(i),(opt.copy?cs[2+((neg(i)-2)%2)]:cs[neg(i)]),0);
 let I=opt.copy?2+(i-2)%2:i; let sw=A[i].length;
 if(!opt.noOld){edge(i,i,i,opt.dx!=null&&I===2?opt.dx:19*I+3+trial*(I+12)**2,1);edge(i,i,neg(i),7*I+2+trial*(7*I+2)**2,1); if(opt.flips){edge(i,neg(i),i,71*I+9,1);edge(i,neg(i),neg(i),61*I+20,1);}
 for(let k=0;k<2;k++)for(let j=0;j<2;j++)edge(i,j,k,((I+13*k+73*j)**2+trial*(11*I+3*k+5*j)**3)%1009,1);}
 if(opt.passive && i>=4)A[i].splice(sw);
 if(opt.mark===i>>1){edge(i,i,0,i**3%1009,1);edge(i,i,1,i**2%1009,1);}
 }
 let w=Array(8); function dfs(s,i,a,b,d){
 if(i==8){if(a!=s)return;let ri=code([w[0],w[2],w[4],w[6]]),rc=idx[ri];if(rc<0||code(reps[rc])!=ri)return;
 let ci=code([neg(w[1]),neg(w[3]),neg(w[5]),neg(w[7])]),cc=idx[ci];if(cc>=0)M[d][rc][cc]+=b*wt[ci];return;}
 for(let [j,k,c,t] of A[a])if(t+d<=D){w[i]=k;dfs(s,i+1,j,b*c%p,d+t);}
 }
 for(let s=0;s<q;s++)dfs(s,0,s,1,0);return [B,M.map(a=>a.map(r=>r.map(mod)))]
}
function eliminate(B,M){let {reps,grp,abs,signed}=B;
 let br=[],bc=[],kr=[],kc=[],Bs=[];
 for(let [key,ids] of grp){let m=sub(M[0],ids,ids),{rows,cols}=gauss(m),br0=rows.map(j=>ids[j]),bc0=cols.map(j=>ids[j]),ib=inverse(sub(M[0],br0,bc0));Bs.push([br.length,ib]);br.push(...br0);bc.push(...bc0);
 let letters=key?key.split(',').map(Number):[];
 let keep= letters.every(a=>letters.filter(b=>b==a).length==letters.filter(b=>b==neg(a)).length);
 if (letters.length%2 && rows.length!=ids.length)throw Error("odd intermediate "+key);
 if(keep){kr.push(...ids.filter(i=>!br0.includes(i)));kc.push(...ids.filter(i=>!bc0.includes(i)));}}
 let ib=of(br.length,br.length);for(let [k,b] of Bs)for(let i=0;i<b.length;i++)for(let j=0;j<b.length;j++)ib[k+i][k+j]=b[i][j];
 let A=M.map(m=>sub(m,br,bc)),J=M.map(m=>sub(m,br,kc)),C=M.map(m=>sub(m,kr,bc)),D=M.map(m=>sub(m,kr,kc));
 let X=[],E=[];
 for(let h=0;h<M.length;h++){let b=J[h];for(let j=1;j<=h;j++)b=plus(b,mul(A[j],X[h-j]),-1);X.push(mul(ib,b));
 let w=D[h];for(let j=0;j<=h;j++)w=plus(w,mul(C[j],X[h-j]),-1);E.push(w);}
 return [kr.map(i=>signed[i]),kc.map(i=>signed[i]),E,kr.map(i=>reps[i]),kc.map(i=>reps[i])];
}

const eq=(a,b)=>JSON.stringify(a)==JSON.stringify(b);
const concat=(a,b)=>a.map((r,i)=>r.concat(b[i]));
function extract(q,z=1008){let [r,c,S,R,C]=eliminate(...jets(q,z,2,{copy:true}));if(S[1].some(row=>row.some(Boolean)))throw Error("bad first");
 let K=r.flatMap((x,i)=>x.split(',').length==4?[i]:[]),F=r.flatMap((x,i)=>x.split(',').length==4?[]:[i]);if(!K.length)return {r,c,w:S[2]};
 let H=sub(S[2],K,K);if(gauss(H).k!=K.length)throw Error("H singular");
 let w=plus(sub(S[2],F,F),mul(mul(sub(S[2],F,K),inverse(H)),sub(S[2],K,F)),-1);let divs=[...new Set(K.map(i=>r[i]))].map(k=>{const L=K.flatMap((i,j)=>r[i]===k?[j]:[]);return [k,det(sub(H,L,L))]});return {divs,r:F.map(i=>r[i]), c:F.map(i=>c[i]),w,R:F.map(i=>R[i]),C:F.map(i=>C[i])};}
function det(a){a=a.map(r=>r.slice());let d=1;for(let j=0;j<a.length;j++){let i=a.findIndex((r,k)=>k>=j&&r[j]);if(i<0)return 0;if(i!==j){[a[i],a[j]]=[a[j],a[i]];d=mod(-d)}const t=a[j][j],u=inv(t);d=mod(d*t);for(let k=j+1;k<a.length;k++){const z=mod(a[k][j]*u);for(let l=j;l<a.length;l++)a[k][l]=mod(a[k][l]-z*a[j][l]);}}return d;}
function run(){let {w:w4,divs:d4}=extract(4),{w:w6,R,C,divs:d6}=extract(6);
 let v=[0,1],i=[2,3],j=[4,5];
 let G=sub(w4,v,v),D=sub(w4,v,i),F=sub(w4,i,v),A=sub(w4,i,i),B=plus(sub(w6,i,i),A,-1),C1=sub(w6,i,j);
 if(!eq(sub(w6,v,v),plus(G,G))|| !eq(sub(w6,v,i),D) || !eq(sub(w6,v,j),D)|| !eq(sub(w6,i,v),F)||!eq(sub(w6,j,v),F)||!eq(sub(w6,j,j),sub(w6,i,i))||!eq(sub(w6,j,i),C1))throw Error("not symmetric! "+JSON.stringify({w4,w6,R,C}));
 let bad=[];
 for(let r=0;r<1009;r++){
  let X=plus(A,B,r-1),std=plus(X,C1,-1),triv=concat(G,D).concat(concat(F,plus(X,C1,r-1)));
  if(gauss(std).k<2||gauss(triv).k<4)bad.push(r);
 }
 let Zi=extract(4,469).w,Zm=extract(4,540).w;
 if(!Zi[0][0]||!Zm[0][0])throw Error("bad imaginary sector");return {trial,d4,d6,A,B,C1,G,F,D,bad,Zi,Zm};
}

const expectedBad=[[652],[395]],expectedDiv=[[822,576],[294,274]],expectedIm=[[640,522],[46,624]];
for(trial=0;trial<2;trial++) {
 const z=run();
 if(!eq(z.bad,expectedBad[trial])||!eq(z.d6.map(x=>x[1]),[expectedDiv[trial][0],expectedDiv[trial][1],expectedDiv[trial][0]])||!eq([z.Zi[0][0],z.Zm[0][0]],expectedIm[trial]))throw Error('certificate changed');
 console.log(JSON.stringify(z));
 if(process.argv.includes('--audit-q8')){
  const {w,divs}=extract(8), R=[0,1], E=j=>[2+2*j,3+2*j];
  if(w.length!==8||!eq(sub(w,R,R),plus(plus(z.G,z.G),z.G)))throw Error('q8 core');
  for(let i=0;i<3;i++){
   if(!eq(sub(w,R,E(i)),z.D)||!eq(sub(w,E(i),R),z.F))throw Error('q8 offcore');
   for(let j=0;j<3;j++)if(!eq(sub(w,E(i),E(j)),i===j?plus(z.A,z.B,2):z.C1))throw Error('q8 repeated');
  }
  console.log('AUDIT_Q8_PATTERN',trial,divs);
 }
}

