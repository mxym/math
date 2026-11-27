'use strict';
// Exact size-26 five-uniform pencils under plane cap four.
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));const inv=i;
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

const basis=r.slice(0,8).map(j=>{
 let C=[1],t=1;
 for(let i=0;i<8;i++)if(i!==j){t=m(t*(j-i));const N=Array(C.length+1).fill(0);for(let k=0;k<C.length;k++){N[k]-=i*C[k];N[k+1]+=C[k];}C=N.map(m);}
 return C.map(x=>m(x*inv[t]));
});
const evalPoly=(c,x)=>c.reduceRight((z,a)=>m(x*z+a),0),table=r.slice(8).map(x=>basis.map(c=>evalPoly(c,x)));
const T=[],cat={4:[],5:[],6:[],7:[]}, counts={};
function gen(j,total){
 if(j<8){
  for(let y=0;y<=4;y++){T.push(y);gen(j+1,total+y);T.pop();}
  return;
 }
 if(total<6||total>26)return;
 for(let row of table){let v=m(row.reduce((s,a,k)=>s+a*T[k],0));if(v>4||total+v>26)return;total+=v;}
 if(total!==26)return;
 let C=basis[0].map((_,i)=>m(basis.reduce((s,B,k)=>s+B[i]*T[k],0))),k=C.findLastIndex(x=>x);
 counts[k]=(counts[k]??0)+1;
 if(k>=4)cat[k].push(C);
}
gen(0,0);

const masks={};
function choose(A,k){if(A.length===9){let [j,t]=canonical(A);masks[j]=t;return;}for(let x=k;x<=13-(9-A.length);x++)choose([...A,x],x+1);}choose([0,1,13],2);
const tb=r.map(()=>r.map(()=>[]));
for(const C of cat[7])if(!C[6])tb[C[7]][C[5]].push(C);
const coords=(x,y,z)=>z===13?y:m(x+z*y);
function run(S){
 const F=S.map(s=>V[s]),a=solveCols(F,7,9)([1]),B=solveCols(F,5,9);
 let feas=0,tuples=0,valid=0,first;
 for(let j of r)for(let k of r)for(let l of r){
  const b=B([j,k,l]);if(m(a.reduce((s,x,i)=>s+x*b[i],0)))continue;
  const L=a.map((x,i)=>tb[x][b[i]]);if(L.some(l=>l.length===0))continue;feas++;
  const C=L.map((p,j)=>p.map(c=>({c,v:[0,1,2,3,4].flatMap(d=>Array.from({length:d+1},(_,h)=>m(bin(d,h)*F[j][0]**(d-h)*F[j][1]**h*c[d])))})));
  const tab=new Map(),zero=Array(15).fill(0);
  function side(k,end,u,T){
   if(k===end){
    if(end===4){const w=u.join();if(!tab.has(w))tab.set(w,[]);tab.get(w).push(T);}
    else{const w=u.map((x,j)=>m((j===0?16:0)-x)).join();
     for(const U of tab.get(w)??[]){
      tuples++;
      const P=[...U,...T];let ok=true;
      for(let x of r)for(let y of r){let v=(P.reduce((s,c,j)=>s+evalPoly(c,coords(x,y,S[j])),0)-16)/13;
       if(!Number.isInteger(v)||v<0||v>2){ok=false;break;}}
      if(ok){valid++;first??=P;}
     }}
    return;
   }
   for(const {c,v} of C[k])side(k+1,end,u.map((x,i)=>m(x+v[i])),[...T,c]);
  }
  side(0,4,zero,[]);side(4,9,zero,[]);
 }
 return {S,feas,tuples,valid,first};
}
const result=Object.values(masks).map(run);
 if(JSON.stringify(counts)!==JSON.stringify({0:1,5:156,6:286,7:3120}))throw Error('profile census');
 for(const f of cat[5])if(r.reduce((s,x)=>{const y=evalPoly(f,x);return s+y*(y-1)/2;},0)!==26)throw Error('quintic weight');
 if(result.length!==3||result.some(q=>q.tuples!==0)||result.map(q=>q.feas).join()!=='238,218,223')throw Error('tight-pencil counts');
 console.log({counts,result});

})();
(function(){

'use strict';
const p=13,r=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p,i=r.map(a=>r.find(b=>m(a*b)===1));const inv=i;
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

const basis=r.slice(0,8).map(j=>{
 let C=[1],t=1;
 for(let i=0;i<8;i++)if(i!==j){t=m(t*(j-i));const N=Array(C.length+1).fill(0);for(let k=0;k<C.length;k++){N[k]-=i*C[k];N[k+1]+=C[k];}C=N.map(m);}
 return C.map(x=>m(x*inv[t]));
});
const evalPoly=(c,x)=>c.reduceRight((z,a)=>m(x*z+a),0),table=r.slice(8).map(x=>basis.map(c=>evalPoly(c,x)));
const T=[],cat={4:[],5:[],6:[],7:[]}, counts={};
function gen(j,total){
 if(j<8){
  for(let y=0;y<=4;y++){T.push(y);gen(j+1,total+y);T.pop();}
  return;
 }
 if(total<6||total>26)return;
 for(let row of table){let v=m(row.reduce((s,a,k)=>s+a*T[k],0));if(v>4||total+v>26)return;total+=v;}
 if(total!==26)return;
 let C=basis[0].map((_,i)=>m(basis.reduce((s,B,k)=>s+B[i]*T[k],0))),k=C.findLastIndex(x=>x);
 counts[k]=(counts[k]??0)+1;
 if(k>=4)cat[k].push(C);
}
gen(0,0);

const masks={};
function choose(A,k){if(A.length===9){let [j,t]=canonical(A);masks[j]=t;return;}for(let x=k;x<=13-(9-A.length);x++)choose([...A,x],x+1);}choose([0,1,13],2);

const tb=r.map(()=>r.map(()=>r.map(()=>[])));
for(const C of [...cat[5],...cat[6]])tb[C[6]][C[5]][C[4]].push(C);
const coords=(x,y,z)=>z===13?y:m(x+z*y);
function run(S){
 const F0=S.map(s=>V[s]),A=solveCols(F0,6,9);
 let leads=0,feas5=0,feas4=0,tuples=0,valid=0,first;
 for(let b of r)for(let c of r){
  if(!b&&!c)continue;
  if((b||c)>6)continue; // ± normalizations by global dilation
  const a_=A([b,c]);
  if(m(a_.reduce((s,a)=>s+a*a,0)))continue;
  const ix=[...r.slice(0,9)].sort((i,j)=>+(a_[j]!==0)-+(a_[i]!==0));
  const a=ix.map(i=>a_[i]),F=ix.map(i=>F0[i]),SL=ix.map(i=>S[i]),B=solveCols(F.slice(2),5,7),C=solveCols(F,4,9);
  if(a.filter(Boolean).length<8)throw Error("sextic rank");
  leads++;
  for(let j of r){
   const b=[0,0,...B([j])],LL=a.map((x,i)=>tb[x][b[i]]);
   const CC=LL.map(q=>q.flatMap((l,i)=>l.length?[i]:[]));
   if(CC.some(q=>!q.length))continue;feas5++;
   for(const x of CC[5])for(const y of CC[6])for(const w of CC[7])for(const t of CC[8]){
    const c=C([x,y,w,t]),L=LL.map((q,i)=>q[c[i]]);
    if(L.some(l=>l.length===0))continue;feas4++;
    const C2=L.map((p,j)=>p.map(c=>({c,v:[0,1,2,3].flatMap(d=>Array.from({length:d+1},(_,h)=>m(bin(d,h)*F[j][0]**(d-h)*F[j][1]**h*c[d])))})));
    const tab=new Map(),zero=Array(10).fill(0);
    function side(k,end,u,T){
     if(k===end){
      if(end===4){const w=u.join();if(!tab.has(w))tab.set(w,[]);tab.get(w).push(T);}
      else{const w=u.map((x,j)=>m((j===0?16:0)-x)).join();
       for(const U of tab.get(w)??[]){
        tuples++;
        const P=[...U,...T];let ok=true;
        for(let x of r)for(let y of r){let v=(P.reduce((s,c,j)=>s+evalPoly(c,coords(x,y,SL[j])),0)-16)/13;
         if(!Number.isInteger(v)||v<0||v>2){ok=false;break;}}
        if(ok){valid++;first??=P;}
       }}
      return;
     }
     for(const {c,v} of C2[k])side(k+1,end,u.map((x,i)=>m(x+v[i])),[...T,c]);
    }
    side(0,4,zero,[]);side(4,9,zero,[]);
   }
  }
 }
 return {S,leads,feas5,feas4,tuples,valid,first};
}
const result=Object.values(masks).map(run);
 if(JSON.stringify(counts)!==JSON.stringify({0:1,5:156,6:286,7:3120}))throw Error('profile census');
 for(const f of cat[5])if(r.reduce((s,x)=>{const y=evalPoly(f,x);return s+y*(y-1)/2;},0)!==26)throw Error('quintic weight');
 if(result.length!==3||result.some(q=>q.tuples!==0)||result.map(q=>q.leads).join()!=='84,84,84'||result.map(q=>q.feas5).join()!=='0,24,0'||result.map(q=>q.feas4).join()!=='0,36,0')throw Error('tight-pencil counts');
 console.log({counts,result});

})();
