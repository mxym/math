'use strict';
// Exact symbolic checks. The full side sees only a list of component orders.
// Edges are listed as [parent,child], with every parent preceding its child.
const add=(M,k,v=1)=>M.set(k,(M.get(k)||0)+v);
const check=(ok,msg)=>{if(!ok)throw Error(msg);};
function partitions(N,edges,visit) {
  const par=new Int32Array(N);
  for(const [a,b] of edges){check(a<b,'bad parent order');par[b]=a;}
  const sz=new Int32Array(N), parts=new Int32Array(N);
  for(let m=0;m<2**(N-1);m++){
    sz.fill(1); let k=0;
    for(let v=N-1;v>0;v--){
      if(m&(1<<(v-1)))parts[k++]=sz[v];
      else sz[par[v]]+=sz[v];
    }
    parts[k++]=sz[0]; visit(parts,k,m);
  }
}
function make(block){
  const E=[];let n=1;
  for(const kind of block){
    const a=n++; E.push([0,a]);
    if(kind!=='L')E.push([a,n++]);
    if(kind==='P')E.push([a+1,n++]); // endpoint-rooted 3-path
    if(kind==='V')E.push([a,n++]);   // center-rooted 3-path
  }
  return {E,n};
}
function key(root,high,lo){
  return root+'|'+high.sort().join(',')+'|'+lo.sort().join(',');
}
function run(name,h,g,core,patterns,marked){
  const q=patterns.length, B=patterns.map(make), N=B.reduce((a,b)=>a+b.n,0);
  const big=Array.from(patterns[marked]).filter(c=>h===3?'VP'.includes(c):c==='D').length;
  const edges=core.slice();let next=q;
  for(let v=0;v<q;v++){
    const off=next-1;next+=B[v].n-1;
    edges.push(...B[v].E.map(([a,b])=>[a===0?v:a+off,b+off]));
  }
  const actual=new Map;
  partitions(N,edges,(p,k)=>{
    let hits=0;
    for(let i=0;i<k;i++)if(p[i]===h)hits++;
    if(hits!==1)return;
    let root=0,M=0;const hi=[],lo=[];
    for(let i=0;i<k;i++){
      const a=p[i];
      if(a>h){
        const n=g*Math.ceil(a/g),d=n-a;
        if(d>h)return;
        M+=n;
        if(d===h){if(root)return;root=n;}
        else hi.push(n+':'+d);
      } else if(a<h) lo.push(a);
    }
    if(root&&M===N)add(actual,key(root,hi,lo));
  });

  const expected=new Map;
  const prof=B.map((b,v)=>{
    const out=new Map;
    if(v===marked)return [['',1]];
    partitions(b.n,b.E,(p,k)=>{
      const d=b.n-p[k-1]; if(d>=h)return;
      add(out,Array.from(p.slice(0,k-1)).sort().join(','));
    });
    return Array.from(out);
  });
  for(let m=0;m<2**(q-1);m++){
    const P=Array.from({length:q},(_,i)=>i);
    const find=v=>P[v]===v?v:find(P[v]);
    for(let j=0;j<core.length;j++)if(!(m&(1<<j))){
      const [u,v]=core[j];P[find(v)]=find(u);
    }
    const G=new Map;
    for(let v=0;v<q;v++){
      const r=find(v); if(!G.has(r))G.set(r,[]);
      G.get(r).push(v);
    }
    const mass=A=>A.reduce((a,v)=>a+B[v].n,0);
    const rootG=find(marked), root=mass(G.get(rootG));
    const other=Array.from(G).filter(([r])=>r!==rootG).map(([,A])=>A);
    function choices(j,hi,lo,c){
      if(j===other.length){add(expected,key(root,hi.slice(),lo.slice()),c*big);return;}
      const A=other[j],n=mass(A);
      function jets(i,low,d,w){
        if(i===A.length){choices(j+1,[...hi,n+':'+d],[...lo,...low],c*w);return;}
        for(const [s,k] of prof[A[i]]){
          const xs=s?s.split(',').map(Number):[],e=d+xs.reduce((a,z)=>a+z,0);
          if(e<h)jets(i+1,[...low,...xs],e,w*k);
        }
      }
      jets(0,[],0,1);
    }
    choices(0,[],[],1);
  }
  check(actual.size===expected.size,name+' support');
  for(const [k,v] of expected)check(actual.get(k)===v,name+' '+k+' '+actual.get(k)+' vs '+v);
  return [name,2**(N-1),actual.size];
}
const runs=[
  run('h=2 claw / repeated ordinary',2,5,[[0,1],[0,2],[0,3]],['DD','LLLL','LLLL','LLLL'],0),
  run('h=3 mark at leaf / repeated maximum / varied ordinary',3,8,[[0,1],[1,2]],['PVL','LLLLLLL','DDDL'],0),
  run('h=2 unequal orders',2,3,[[0,1]],['DDL','LLLLLLLL'],0),
];
for(const r of runs) (typeof console==='undefined'?text:console.log)(r.join(' | '));
