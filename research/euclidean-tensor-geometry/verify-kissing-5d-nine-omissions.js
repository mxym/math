const MAX=9;
function dot(a, b) {
  return a.reduce((sum,v,i)=>sum+v*b[i],0n);
}

// Fraction-free determinant with exact row pivoting.
function det(rows) {
  const a=rows.map(row=>row.slice());
  let sign=1n, prev=1n;
  for(let j=0;j<a.length-1;j++){
    const pivot=a.findIndex((row,i)=>i>=j&&row[j]!==0n);
    if(pivot<0)return 0n;
    if(pivot!==j){[a[j],a[pivot]]=[a[pivot],a[j]];sign=-sign;}
    for(let i=j+1;i<a.length;i++)for(let k=j+1;k<a.length;k++){
      const num=a[i][k]*a[j][j]-a[i][j]*a[j][k];
      if(num%prev!==0n)throw Error('division');
      a[i][k]=num/prev;
    }
    for(let i=j+1;i<a.length;i++)a[i][j]=0n;
    prev=a[j][j];
  }
  return sign*a.at(-1).at(-1);
}

const R=Array.from({length:5},(_,i)=>Array.from({length:5-i-1},(_,n)=>[1,-1].map(sign=>Array.from({length:5},(_,k)=>k===i?1:k===i+1+n?sign:0)))).flat(2);
const roots=R.concat(R.map(v=>v.map(x=>-x)));const I=[0,1,2,3,4,5],basis=I.map(i=>I.map(j=>i===j?1n:0n));
const B=R.map(r=>I.map(i=>i===5?0n:BigInt(r.slice(0,i+1).reduce((x,y)=>x+y,0))));
const ids=R.map((_,i)=>i),maximal=C=>C.filter(i=>!C.some(j=>i!==j&&B[j].every((x,k)=>x>=B[i][k]))),minimal=C=>C.filter(i=>!C.some(j=>i!==j&&B[j].every((x,k)=>x<=B[i][k])));
function vertices(C){
 const N=maximal(ids.filter(i=>!C.includes(i))),P=minimal(C);const rows=basis.map(v=>v.map(x=>-x)).concat(N.map(i=>B[i]),P.map(i=>B[i].map(x=>-x)),[[0n,0n,0n,0n,0n,1n],[2n,2n,2n,2n,2n,0n]]),rhs=basis.map(()=>0n).concat(N.map(()=>1n),P.map(()=>-1n),[0n,3n]),map=new Map();
 const walk=(A,from)=>{if(A.length!==6){for(let i=from;i<=rows.length-6+A.length;i++)walk(A.concat([i]),i+1);return;}
 const M=A.map(i=>rows[i]),v=A.map(i=>rhs[i]);let D=det(M);if(!D)return;let nums=I.map(k=>det(M.map((r,i)=>r.map((x,j)=>j===k?v[i]:x))));if(D<0n){D=-D;nums=nums.map(x=>-x);}if(rows.some((r,i)=>dot(r,nums)>rhs[i]*D))return;
 const gcd=(a,b)=>b?gcd(b,a%b):a;const g=nums.reduce((g,x)=>gcd(g,x),D);nums=nums.map(x=>x/g);D/=g;const a=I.map(i=>i===5?nums[5]:nums.slice(i,5).reduce((v,w)=>v+w,0n));map.set(String(a)+'/'+D,{a,D});
 };walk([],0);return [...map.values()];
}
const q=v=>3n*v.a.slice(0,5).reduce((s,x)=>s+x*x,0n)+v.a[5]**2n,rootPt=v=>v.a[5]===0n&&v.a.slice(0,5).filter(z=>z===v.D).length===2&&v.a.slice(0,5).every(z=>z===v.D||z===0n);
const exact=(v,C)=>R.every((r,i)=>(r.reduce((s,x,k)=>s+BigInt(x)*v.a[k],0n)>v.D)===C.includes(i));
let cur=[[]];const types=[];for(let k=0;k<=MAX;k++){let count=0;for(const C of cur){const V=vertices(C);const hi=V.filter(v=>q(v)>6n*v.D**2n),eq=V.filter(v=>q(v)===6n*v.D**2n&&!rootPt(v)&&exact(v,C));
 if(hi.length||eq.length){count++;types.push({k,C,V:hi.length?V:eq});}
 }console.log({k,ideals:cur.length,possible:count});const nxt=new Map();for(const C of cur)for(const i of maximal(ids.filter(i=>!C.includes(i)))){const D=C.concat(i).sort((a,b)=>a-b);nxt.set(D.join(),D);}cur=[...nxt.values()];}

const A=[0,1,2,3,4],L=192,dotN=(v,w)=>A.reduce((s,i)=>s+v[i]*w[i],0),normN=v=>dotN(v,v),cut=L*L;
const perm=a=>a.length?a.flatMap((x,i)=>perm(a.filter((_,j)=>j!==i)).map(r=>[x,...r])):[[]];
const gs=[];for(const p of perm(A))for(let m=0;m<32;m++)gs.push(p.map((k,i)=>((m>>i)&1?-1:1)*(k+1)));const act=(v,g)=>g.map(i=>(i<0?-1:1)*v[Math.abs(i)-1]);
const idx=new Map(roots.map((v,i)=>[v.join(),i]));const msk=ids=>ids.reduce((s,i)=>s|1n<<BigInt(i),0n),gp=gs.map(g=>roots.map(v=>idx.get(act(v,g).join()))),neg=roots.map(v=>idx.get(v.map(x=>-x).join()));
const all=new Map();for(const [k,T] of types.entries()){const P=T.V.map(v=>v.a.slice(0,5).map(x=>{if(2n*x%v.D)throw Error('scale');return Number(2n*x/v.D);}));
 const high=P.filter(v=>normN(v)>8),low=P.filter(v=>normN(v)<=8),gen=high.map(x=>x.map(v=>96*v));for(const v of low){if(!high.length){if(normN(v)===8)gen.push(v.map(x=>96*x));continue;}
 let g=96;const mix=(u,t)=>u.map((x,i)=>x*t+v[i]*(96-t));while(high.some(u=>normN(mix(u,g))>2*cut))--g;
 if(normN(v)===8&&g!==0)throw Error('lost equality');for(const u of high)gen.push(mix(u,g));}
 T.h=[...new Map(gen.map(v=>[v.join(),v])).values()];if(T.h.some(v=>v.some(x=>!Number.isSafeInteger(x)||Math.abs(x)>288)))throw Error('safe products');T.root=T.h.map(v=>v[0]>0&&v[0]===v[1]&&v.slice(2).every(x=>x===0));T.ns=T.h.map(normN);T.m=msk(T.C);T.st=[];
 for(const [j,p] of gp.entries()){const C=T.C.map(i=>p[i]),m=msk(C);if(m===T.m)T.st.push(j);let z=all.get(m);if(!z){z={m,k,j,ids:C,ts:[]};all.set(m,z);}if(z.k!==k)throw Error('duplicate orbit');z.ts.push(j);}
}
function excludes(A,B,g){
 const H=B.h.map(v=>act(v,g)),vals=A.h.map(v=>H.map(w=>dotN(v,w)));
 if(vals.every((r,i)=>r.every((u,j)=>u>cut||u===cut&&(A.root[i]||B.root[j]))))return true;
 const rowwise=(T,A,B)=>T.every((r,i)=>r.every((v,j)=>v>=0&&(2*v*v>A.ns[i]*cut||2*v*v===A.ns[i]*cut&&(A.root[i]||B.root[j])))||r.every((v,j)=>v>=0&&(4*v*v>A.ns[i]*B.ns[j]||4*v*v===A.ns[i]*B.ns[j]&&(A.root[i]||B.root[j]))));
 return rowwise(vals,A,B)||rowwise(B.h.map((_,j)=>vals.map(r=>r[j])),B,A);
}
console.log('BAD types',types.map((T,k)=>[k,T.k,T.C,T.h.length,T.st.filter(j=>!excludes(T,T,gs[j])).length]).filter(x=>x[4]));
if(types.some(T=>T.st.some(j=>!excludes(T,T,gs[j]))))throw Error('same mask capacity');
const gidx=new Map(gs.map((g,i)=>[g.join(),i])),gis=gp.map(p=>{const v=[];for(const [i,j] of p.entries())v[j]=i;return v;}),pm=(ids,p)=>msk(ids.map(i=>p[i])),one=roots.map((_,i)=>1n<<BigInt(i));for(const T of types)T.cache=new Map();
function inc(a,b){if(a.k>b.k)[a,b]=[b,a];const T=types[a.k],D=types[b.k],mb=pm(b.ids,gis[a.j]);if(T.cache.has(mb))return T.cache.get(mb);const rec=all.get(mb),orbit=new Set(T.st.map(j=>pm(rec.ids,gp[j])));let no=true;outer:for(const m of orbit)for(const j of all.get(m).ts)if(!excludes(T,D,gs[j])){no=false;break outer;}for(const m of orbit)T.cache.set(m,no);return no;}
const mraw=new Set(),can=new Map(),sMemo=new Map(),stMemo=new Map();
function canonical(U){const m=msk(U);if(mraw.has(m))return;mraw.add(m);
 const sum=A.map(k=>U.reduce((a,i)=>a+roots[i][k],0)),ky=sum.join();let z=sMemo.get(ky);if(!z){const gr=A.slice().sort((i,j)=>Math.abs(sum[j])-Math.abs(sum[i])).map(i=>(sum[i]<0?-1:1)*(i+1)),k=gidx.get(gr.join()),s=act(sum,gr),y=s.join();let st=stMemo.get(y);if(!st){st=gs.map((g,j)=>act(s,g).join()===y?j:-1).filter(i=>i>=0);stMemo.set(y,st);}z=[k,st];sMemo.set(ky,z);}
 const T=U.map(i=>gp[z[0]][i]);let bm=null;for(const j of z[1]){const mm=pm(T,gp[j]);if(can.has(mm))return;if(bm===null||mm<bm)bm=mm;}can.set(bm,roots.map((_,i)=>i).filter(i=>bm&one[i]));
}

for(const T of types)if(T.C.length===3||!types.some(t=>t.C.length<T.C.length&&t.C.every(i=>T.C.includes(i))))canonical(T.C);
for(let m=3;m<MAX;m++){const vs=[...can.values()].filter(U=>U.length===m);for(const U of vs)for(let i=0;i<roots.length;i++)if(!U.includes(i))canonical(U.concat([i]));console.log('level',m,vs.length,'total',can.size);}

const edCache=types.map(()=>new Map());function negEdge(a,b){
 if(a.m&b.m)return false;if(a.k>b.k)[a,b]=[b,a];const na=all.get(msk(a.ids.map(i=>neg[i])));const T=types[na.k],D=types[b.k],mb=pm(b.ids,gis[na.j]),cache=edCache[na.k];if(cache.has(mb))return cache.get(mb);
 const rec=all.get(mb),orbit=new Set(T.st.map(g=>pm(rec.ids,gp[g])));let out=false;outer:for(const m of orbit)for(const k of all.get(m).ts){const ys=D.h.map(v=>act(v,gs[k]));if(T.h.some(v=>ys.some(w=>dotN(v,w)>cut))){out=true;break outer;}}
 for(const m of orbit)cache.set(m,out);return out;
}
const cnts={},rem=[];for(const [mb,U] of can){if(U.length!==MAX)continue;
const V=[];for(let mm=mb;mm;mm=(mm-1n)&mb){const o=all.get(mm);if(o)V.push(o);}
const K=U.length+1;let o=cnts[K];if(!o)o=cnts[K]={raw:0,degree:0,pdeg:0,clique:0,constrained:0,d4:0,edge:0,anchored:0,remain:0};
if(V.length<K){o.raw++;continue;}if(U.some(i=>V.filter(t=>t.m&one[i]).length<2)){o.degree++;continue;}
function degree(V){return U.every(i=>{const z=V.filter(t=>t.m&one[i]);return z.some((a,k)=>z.slice(0,k).some(b=>!inc(a,b)));});}if(!degree(V)){o.pdeg++;continue;}
if(A.some(k=>U.every(i=>roots[i][k]))){o.d4++;continue;}
function go(V,n,S,req){if(n<=0)return !req||U.every(i=>S.filter(t=>t.m&one[i]).length>=2);if(V.length<n)return false;
 if(req&&U.some(i=>S.filter(t=>t.m&one[i]).length+V.filter(t=>t.m&one[i]).length<2))return false;
 const C=[];for(const a of V){const f=C.find(c=>c.every(b=>inc(a,b)));if(f)f.push(a);else C.push([a]);}for(let i=C.length-1;i>=n-1;i--){const prev=C.slice(0,i).flat();for(const a of C[i])if(go(prev.filter(b=>!inc(a,b)),n-1,S.concat([a]),req))return true;}return false;}
const E=[];for(let i=0;i<V.length;i++)for(let j=0;j<i;j++)if(negEdge(V[i],V[j])&&!inc(V[i],V[j]))E.push([V[i],V[j]]);if(!E.length){o.edge++;continue;}
if(!go(V,K,[],false)){o.clique++;continue;}if(!go(V,K,[],true)){o.constrained++;continue;}
if(!E.some(([a,b])=>go(V.filter(c=>c!==a&&c!==b&&!inc(a,c)&&!inc(b,c)),K-2,[a,b],true))){o.anchored++;continue;}o.remain++;rem.push(U);if(rem.length<=12)console.log('candidate',U,V.length);
}console.log({indexed:mraw.size,classes:can.size,cnts,survivors:JSON.stringify(rem)});

const z=cnts[10];if(mraw.size!==368555||can.size!==59453||rem.length||z.raw!==41790||z.degree!==4590||z.pdeg!==116||z.edge!==64||z.clique!==21)throw Error('nine census');
console.log('41 points require at least 10 omitted D5 signs.');
