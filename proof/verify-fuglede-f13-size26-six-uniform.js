'use strict';
// Exact size-26 six-uniform projection exclusions, one mask at cap six and all masks at cap five.
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}

const S=[3,4,5,6,8,9,10,11],F=S.map(s=>V[s]),cat=r.map(()=>r.map(()=>[]));
for(let a=1;a<13;a++)for(let b of r)for(let c of r)for(let d of r)for(let e of r)for(let f of r){
 let n=0,good=true;
 for(let x of r){let y=m(((((a*x*x+b)*x+c)*x+d)*x+e)*x+f);if(y>6||n+y>26){good=false;break;}n+=y;}
 if(good&&n===26)cat[a][b].push([f,e,d,c,b,0,a]);
}
const Ax=solveCols(F,6,8),Bx=solveCols(F,4,8);
let nFeas=0,tuples=0,valid=0,gridHist={},first;
for(let a8=1;a8<=6;a8++) {
 const a=Ax([a8]);
 for(let j of r)for(let k of r)for(let l of r){
  const B=Bx([j,k,l]);
  const L=a.map((aj,i)=>cat[aj][B[i]]);
  if(L.some(x=>x.length===0))continue;
  nFeas++;
  const L2=L.map((q,j)=>q.map(co=>({co,key:[...Array(4).keys()].flatMap(d=>Array.from({length:d+1},(_,h)=>m(bin(d,h)*F[j][0]**(d-h)*F[j][1]**h*co[d])))})));
  const tab=new Map();
  const zero=Array(10).fill(0);
  function side(k,end,S,M){
   if(k===end){
    if(end===4){const key=S.join(); if(!tab.has(key))tab.set(key,[]);tab.get(key).push(M);}
    else{
     const look=S.map((t,i)=>m((i===0?14:0)-t)).join();
     for(const U of tab.get(look)??[]){
      tuples++;
      const C=[...U,...M], hist=[0,0,0];let ok=true;
      for(let x of r)for(let y of r){const v=(C.reduce((s,co,j)=>s+co.reduceRight((r,t)=>m(r*(SLOPES[j]===13?y:x+SLOPES[j]*y)+t),0),0)-14)/13;
       if(!Number.isInteger(v)||v<0||v>2){ok=false;break;} hist[v]++;}
      if(ok){valid++;gridHist[hist.join()]=(gridHist[hist.join()]??0)+1;first??=C;}
     }
    }return;
   }
   for(const o of L2[k])side(k+1,end,S.map((s,i)=>m(s+o.key[i])),[...M,o.co]);
  }
  const SLOPES=S;
  side(0,4,zero,[]);side(4,8,zero,[]);
 }
}
if(nFeas!==921||tuples!==36||valid!==0)throw Error('targeted sextic census');
console.log({nFeas,tuples,valid});

})();
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}


const S=[3,4,5,6,8,9,10,11],F0=S.map(s=>V[s]),cat=r.map(()=>r.map(()=>r.map(()=>[]))),H={};
for(let j of [4,5]){
 function add(c){
  if(c.length<j-1){for(let x of r)add([...c,x]);return;}
  for(let a=1;a<p;a++){
   const C=[...c,0,a], n=r.map(x=>C.reduceRight((q,t)=>m(q*x+t),0));
   if(n.some(y=>y>6)||n.reduce((s,y)=>s+y,0)!==26)continue;
   H[j]=(H[j]??0)+1;
   for(let z of r){
    const B=Array.from({length:6},(_,i)=>m(C.slice(i).reduce((s,a,k)=>s+a*bin(i+k,i)*z**k,0)));
    cat[B[5]][B[4]][B[3]].push(B);
   }
  }
 }
 add([]);
}
const A=solveCols(F0,5,8);
let leads=0,degree4=0,nFeas=0,tuples=0,valid=0,gridHist={},first;
for(let g=0;g<=13;g++){
 const a_=A(g<13?[1,g]:[0,1]),ix=[...r.slice(0,8)].sort((i,j)=>+(a_[j]!==0)-+(a_[i]!==0));
 const a=ix.map(i=>a_[i]),F=ix.map(i=>F0[i]),SL=ix.map(i=>S[i]);
 if(a.filter(Boolean).length<7)throw Error("leading coordinates");
 leads++;
 const B=solveCols(F.slice(2),4,6),C=solveCols(F,3,8);
 for(const z of r){
  const b=[0,0,...B([z])];
  let K=a.map((a,i)=>cat[a][b[i]]);
  if(K.some(L=>L.every(x=>x.length===0)))continue;
  degree4++;
  const CS=K.map(L=>L.flatMap((x,i)=>x.length?[i]:[]));
  for(const x of CS[4])for(const y of CS[5])for(const w of CS[6])for(const t of CS[7]){
   const c=C([x,y,w,t]),L=K.map((q,i)=>q[c[i]]);
   if(L.some(l=>l.length===0))continue;
   nFeas++;
   const L2=L.map((q,i)=>q.map(co=>({co,key:[...Array(3).keys()].flatMap(d=>Array.from({length:d+1},(_,h)=>m(bin(d,h)*F[i][0]**(d-h)*F[i][1]**h*co[d])))})));
   const tab=new Map(),zero=Array(6).fill(0);
   function side(k,end,S,M){
    if(k===end){
     if(end===4){const key=S.join();if(!tab.has(key))tab.set(key,[]);tab.get(key).push(M);}
     else{
      const look=S.map((t,i)=>m((i===0?14:0)-t)).join();
      for(const U of tab.get(look)??[]){
       tuples++;
       const C=[...U,...M],hist=[0,0,0];let ok=true;
       for(let x of r)for(let y of r){const v=(C.reduce((s,co,j)=>s+co.reduceRight((r,t)=>m(r*(x+SL[j]*y)+t),0),0)-14)/13;
        if(!Number.isInteger(v)||v<0||v>2){ok=false;break;}hist[v]++;}
       if(ok){valid++;gridHist[hist.join()]=(gridHist[hist.join()]??0)+1;first??=C;}
      }
     }
     return;
    }
    for(const o of L2[k])side(k+1,end,S.map((s,i)=>m(s+o.key[i])),[...M,o.co]);
   }
   side(0,4,zero,[]);side(4,8,zero,[]);
  }
 }
}
if(H[4]!==9||H[5]!==36||leads!==14||degree4!==126||nFeas!==138||tuples!==0||valid!==0)throw Error('targeted quintic census');
console.log({H,leads,degree4,nFeas,tuples,valid});

})();
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}


const S=[3,4,5,6,8,9,10,11],F0=S.map(s=>V[s]),cat=r.map(()=>r.map(()=>r.map(()=>[]))),H={};
for(let j of [4,5]){
 function add(c){
  if(c.length<j-1){for(let x of r)add([...c,x]);return;}
  for(let a=1;a<p;a++){
   const C=[...c,0,a], n=r.map(x=>C.reduceRight((q,t)=>m(q*x+t),0));
   if(n.some(y=>y>6)||n.reduce((s,y)=>s+y,0)!==26)continue;
   H[j]=(H[j]??0)+1;
   for(let z of r){
    const B=Array.from({length:6},(_,i)=>m(C.slice(i).reduce((s,a,k)=>s+a*bin(i+k,i)*z**k,0)));
    cat[B[5]][B[4]][B[3]].push(B);
   }
  }
 }
 add([]);
}

const A=solveCols(F0,4,8),B=solveCols(F0.slice(2),3,6),leading=cat[0].flatMap((l,i)=>l.some(d=>d.length)?[i]:[]);
let peaks=0,degree3=0,tuples=0,valid=0,gridHist={},first;
for(const u of leading)for(const v of leading)for(const t of leading){
 const a=A([u,v,t]);if(a.some(x=>!leading.includes(x)))continue;
 peaks++;
 const lists=a.map(A=>cat[0][A].flatMap((q,i)=>q.length?[i]:[]));
 for(const s of lists[6])for(const t of lists[7]){
  const b=[0,0,...B([s,t])],L=a.map((a,i)=>cat[0][a][b[i]]);
  if(L.some(q=>q.length===0))continue;
  degree3++;
  let T=[]; 
  function test(j){
   if(j===8){
    let C0=0,Cx=0,Cy=0,Cxx=0,Cxy=0,Cyy=0;
    for(let j=0;j<8;j++){const f=T[j],s=S[j];C0+=f[0];Cx+=f[1];Cy+=s*f[1];Cxx+=f[2];Cxy+=s*f[2];Cyy+=s*s*f[2];}
    if(m(C0-14)||m(Cx)||m(Cy)||m(Cxx)||m(Cxy)||m(Cyy))return;
    tuples++;
    const hist=[0,0,0];let ok=true;
    for(let x of r)for(let y of r){const v=(T.reduce((s,co,j)=>s+co.reduceRight((r,t)=>m(r*(x+S[j]*y)+t),0),0)-14)/13;
     if(!Number.isInteger(v)||v<0||v>2){ok=false;break;}hist[v]++;}
    if(ok){valid++;gridHist[hist.join()]=(gridHist[hist.join()]??0)+1;first??=T.slice();}return;
   }
   for(const e of L[j]){T.push(e);test(j+1);T.pop();}
  }
  test(0);
 }
}
if(peaks!==0)throw Error('targeted quartic leading coefficients');
console.log({peaks});

})();
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}

const masks={};
function choose(S,k){if(S.length===8){let [j,t]=canonical(S);masks[j]=t;return;}for(let x=k;x<=13-(8-S.length);x++)choose([...S,x],x+1);}choose([0,1,13],2);
const cat=r.map(()=>r.map(()=>[]));
for(let a=1;a<13;a++)for(let b of r)for(let c of r)for(let d of r)for(let e of r)for(let f of r){
 let n=0,good=true;
 for(let x of r){let y=m(((((a*x*x+b)*x+c)*x+d)*x+e)*x+f);if(y>5||n+y>26){good=false;break;}n+=y;}
 if(good&&n===26)cat[a][b].push([f,e,d,c,b,0,a]);
}
function run(S){
const F=S.map(s=>V[s]),Ax=solveCols(F,6,8),Bx=solveCols(F,4,8);
let nFeas=0,tuples=0,valid=0,gridHist={},first;
for(let a8=1;a8<=6;a8++) {
 const a=Ax([a8]);
 for(let j of r)for(let k of r)for(let l of r){
  const B=Bx([j,k,l]);
  const L=a.map((aj,i)=>cat[aj][B[i]]);
  if(L.some(x=>x.length===0))continue;
  nFeas++;
  const L2=L.map((q,j)=>q.map(co=>({co,key:[...Array(4).keys()].flatMap(d=>Array.from({length:d+1},(_,h)=>m(bin(d,h)*F[j][0]**(d-h)*F[j][1]**h*co[d])))})));
  const tab=new Map();
  const zero=Array(10).fill(0);
  function side(k,end,S,M){
   if(k===end){
    if(end===4){const key=S.join(); if(!tab.has(key))tab.set(key,[]);tab.get(key).push(M);}
    else{
     const look=S.map((t,i)=>m((i===0?14:0)-t)).join();
     for(const U of tab.get(look)??[]){
      tuples++;
      const C=[...U,...M], hist=[0,0,0];let ok=true;
      for(let x of r)for(let y of r){const v=(C.reduce((s,co,j)=>s+co.reduceRight((r,t)=>m(r*(SLOPES[j]===13?y:x+SLOPES[j]*y)+t),0),0)-14)/13;
       if(!Number.isInteger(v)||v<0||v>2){ok=false;break;} hist[v]++;}
      if(ok){valid++;gridHist[hist.join()]=(gridHist[hist.join()]??0)+1;first??=C;}
     }
    }return;
   }
   for(const o of L2[k])side(k+1,end,S.map((s,i)=>m(s+o.key[i])),[...M,o.co]);
  }
  const SLOPES=S;
  side(0,4,zero,[]);side(4,8,zero,[]);
 }
}
return {S,nFeas,tuples,valid,gridHist,first};}
const result=Object.values(masks).map(run);if(result.map(q=>q.nFeas).join()!=='38,2,12,91,76'||result.some(q=>q.tuples!==0))throw Error('cap5 sextic census');
console.log(result);

})();
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));
const V=[...r.map(s=>[1,s]),[0,1]];
const det=([a,b],[c,d])=>m(a*d-b*c);
const code=A=>A.reduce((z,x)=>z*14+x,0);
function canonical(S){let best=Infinity,out;
 for(const a of S)for(const b of S)for(const c of S)if(a!==b&&a!==c&&b!==c){
  const s=det(V[c],V[a])*i[det(V[c],V[b])];
  const seq=S.map(k=>{const den=det(V[k],V[a]);return den?m(det(V[k],V[b])*s*i[den]):13;}).sort((a,b)=>a-b);
  const cd=code(seq);if(cd<best){best=cd;out=seq;}
 }return [best,out];
}
const bin=(n,k)=>{let b=1;for(let c=1;c<=k;c++)b=b*(n-c+1)/c;return b;};
function solveCols(D,d,n){const M=Array.from({length:d+1},(_,k)=>D.map(([a,b])=>m(bin(d,k)*a**(d-k)*b**k)));
 for(let j=0;j<=d;j++){let k=M.findIndex((u,t)=>t>=j&&u[j]);if(k<0)throw Error("Vdm");
  [M[k],M[j]]=[M[j],M[k]];let w=i[M[j][j]];M[j]=M[j].map(a=>m(w*a));
  for(let t=0;t<=d;t++)if(t!==j){let c=M[t][j];M[t]=M[t].map((a,b)=>m(a-c*M[j][b]));}
 }
 return tail=>[...M.map(row=>m(-tail.reduce((w,t,k)=>w+t*row[d+1+k],0))),...tail];
}


const masks={};
function choose(S,k){if(S.length===8){let [j,t]=canonical(S);masks[j]=t;return;}for(let x=k;x<=13-(8-S.length);x++)choose([...S,x],x+1);}choose([0,1,13],2);
const cat=r.map(()=>r.map(()=>r.map(()=>[]))),H={};
for(let j of [4,5]){
 function add(c){
  if(c.length<j-1){for(let x of r)add([...c,x]);return;}
  for(let a=1;a<p;a++){
   const C=[...c,0,a], n=r.map(x=>C.reduceRight((q,t)=>m(q*x+t),0));
   if(n.some(y=>y>5)||n.reduce((s,y)=>s+y,0)!==26)continue;
   H[j]=(H[j]??0)+1;
   for(let z of r){
    const B=Array.from({length:6},(_,i)=>m(C.slice(i).reduce((s,a,k)=>s+a*bin(i+k,i)*z**k,0)));
    cat[B[5]][B[4]][B[3]].push(B);
   }
  }
 }
 add([]);
}
function run(S){const F0=S.map(s=>V[s]),A=solveCols(F0,5,8);
let leads=0,degree4=0,nFeas=0,tuples=0,valid=0,gridHist={},first;
for(let g=0;g<=13;g++){
 const a_=A(g<13?[1,g]:[0,1]),ix=[...r.slice(0,8)].sort((i,j)=>+(a_[j]!==0)-+(a_[i]!==0));
 const a=ix.map(i=>a_[i]),F=ix.map(i=>F0[i]),SL=ix.map(i=>S[i]);
 if(a.filter(Boolean).length<7)throw Error("leading coordinates");
 leads++;
 const B=solveCols(F.slice(2),4,6),C=solveCols(F,3,8);
 for(const z of r){
  const b=[0,0,...B([z])];
  let K=a.map((a,i)=>cat[a][b[i]]);
  if(K.some(L=>L.every(x=>x.length===0)))continue;
  degree4++;
  const CS=K.map(L=>L.flatMap((x,i)=>x.length?[i]:[]));
  for(const x of CS[4])for(const y of CS[5])for(const w of CS[6])for(const t of CS[7]){
   const c=C([x,y,w,t]),L=K.map((q,i)=>q[c[i]]);
   if(L.some(l=>l.length===0))continue;
   nFeas++;
   const L2=L.map((q,i)=>q.map(co=>({co,key:[...Array(3).keys()].flatMap(d=>Array.from({length:d+1},(_,h)=>m(bin(d,h)*F[i][0]**(d-h)*F[i][1]**h*co[d])))})));
   const tab=new Map(),zero=Array(6).fill(0);
   function side(k,end,S,M){
    if(k===end){
     if(end===4){const key=S.join();if(!tab.has(key))tab.set(key,[]);tab.get(key).push(M);}
     else{
      const look=S.map((t,i)=>m((i===0?14:0)-t)).join();
      for(const U of tab.get(look)??[]){
       tuples++;
       const C=[...U,...M],hist=[0,0,0];let ok=true;
       for(let x of r)for(let y of r){const v=(C.reduce((s,co,j)=>s+co.reduceRight((r,t)=>m(r*(SL[j]===13?y:x+SL[j]*y)+t),0),0)-14)/13;
        if(!Number.isInteger(v)||v<0||v>2){ok=false;break;}hist[v]++;}
       if(ok){valid++;gridHist[hist.join()]=(gridHist[hist.join()]??0)+1;first??=C;}
      }
     }
     return;
    }
    for(const o of L2[k])side(k+1,end,S.map((s,i)=>m(s+o.key[i])),[...M,o.co]);
   }
   side(0,4,zero,[]);side(4,8,zero,[]);
  }
 }
}
return {S,H,leads,degree4,nFeas,tuples,valid,gridHist,first};}
const result=Object.values(masks).map(run);if(Object.keys(H).join()!=='5'||H[5]!==12||result.length!==5||result.some(q=>q.leads!==14||q.degree4!==78||q.nFeas!==0||q.tuples!==0))throw Error('cap5 quintic census');
console.log(result);

})();
