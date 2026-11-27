"use strict";
// Exact certificate for the lower bound 13 in the B-variant of 2LC.
// Run: node --expose-gc verify_factor_littlewood_b13.js
function boundedDoubling(C, maxDepth, maxStates, report) {
  if(!Number.isInteger(C)||!Number.isInteger(maxDepth)||!Number.isInteger(maxStates)||maxDepth<1||maxStates<1||C<1||C>15||(C+1)*2**maxDepth>Number.MAX_SAFE_INTEGER)
    throw Error("exact-integer or run-field range");
  const ID=[1,0,0,1], K=2*C;
  const key=a=>a.join(",");
  function fingerprint(a){let h=0x9e3779b9;for(const v of a){h=Math.imul(h^(v|0),16777619);h=Math.imul(h^Math.floor(v/4294967296),16777619);}return h>>>0;}
  function reduced(a,b,c,d){
    const W=[];
    for(;;){
      if(a>=c&&b>=d){const z=Math.min(c?Math.floor(a/c):Infinity,d?Math.floor(b/d):Infinity);
        a-=z*c;b-=z*d;W.push(0,z);}
      else if(c>=a&&d>=b){const z=Math.min(a?Math.floor(c/a):Infinity,b?Math.floor(d/b):Infinity);
        c-=z*a;d-=z*b;W.push(1,z);}
      else return [[a,b,c,d],W];
    }
  }
  function multiply(A,B){
    const [a,b,c,d]=A,[e,f,g,h]=B;
    return reduced(a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)[0];
  }
  function stepWord(M,p,n){
    const [a,b,c,d]=M;
    return p?reduced(a+n*b,b,c+n*d,d):reduced(a,b+n*a,c,d+n*c);
  }
  function closure(e){
    const S=[[e,0,0,1]], known=new Set([key(S[0])]);
    for (const A of S) for(const p of [0,1]){
      const [B]=stepWord(A,p,1), k=key(B);
      if(!known.has(k)){known.add(k);S.push(B);}
    }
    return S;
  }
  const swap=A=>[A[3],A[2],A[1],A[0]];
  const A2=closure(2), A4=closure(4);
  if(A2.length!==4 || A4.length!==12)throw Error("small transducer closures");
  for(const set of [A2,A4]) {
    const ks=new Set(set.map(key));
    if(set.some(x=>!ks.has(key(swap(x)))))throw Error("letter symmetry");
  }
  function grow(Kind) {
    let u=new Kind(64), at=0;
    return {
      add(x){if(at===u.length){const v=new Kind(u.length*2);v.set(u);u=v;}u[at++]=x;},
      get length(){return at;},
      get array(){return u;},
      view(){return u.subarray(0,at);}
    };
  }
  function exactTable(Wide, initial) {
    const coords=grow(Wide), maskOf=(x,n)=>x&(n-1), size=()=>coords.length/4;
    let slots=new Uint32Array(2**Math.ceil(Math.log2(Math.max(64,initial))));
    function read(i){const a=coords.array,j=4*i;return [a[j],a[j+1],a[j+2],a[j+3]];}
    function exact(j,B){const a=coords.array,z=4*j;return a[z]===B[0]&&a[z+1]===B[1]&&a[z+2]===B[2]&&a[z+3]===B[3];}
    function at(B){let j=maskOf(fingerprint(B),slots.length);while(slots[j]&&!exact(slots[j]-1,B))j=maskOf(j+1,slots.length);return j;}
    function insert(B){
      let z=at(B);if(slots[z])return slots[z]-1;
      if((size()+1)*10>slots.length*7){
        slots=new Uint32Array(slots.length*2);
        for(let j=0;j<size();j++)slots[at(read(j))]=j+1;
        z=at(B);
      }
      const j=size();for(const x of B)coords.add(x);slots[z]=j+1;return j;
    }
    return {insert, lookup(B){return slots[at(B)]-1;}, read, get size(){return size();}, clear(){slots=null;}};
  }
  function pop(x) {
    x-=x>>>1&0x55555555;
    x=(x&0x33333333)+(x>>>2&0x33333333);
    return Math.imul((x+(x>>>4))&0x0f0f0f0f,0x01010101)>>>24;
  }
  function get(A,i){const j=4*i;return [A[j],A[j+1],A[j+2],A[j+3]];}
  let G={mats:Uint32Array.from(ID), oldMats:Uint32Array.from(ID), mi:new Uint32Array(1), pi:new Uint32Array(1),
          ep:Uint32Array.of(0,C), to:new Uint32Array(C), lab:new Uint8Array(C)};
  for(let a=1;a<=C;a++)G.lab[a-1]=a;
  function advance(prev,lev){
    const n=prev.mi.length;
    const baseM=new Uint32Array(4*n), source=new Uint32Array(4*n), bi=new Uint32Array(n+1);
    const T=exactTable(lev<32?Uint32Array:Float64Array,Math.max(64,n));
    let baseN=0, oldL=-1, oldR=-1;
    {
      // Store only the most recent conditioned fibre. The 4-transducer cache
      // uses fingerprints: equality is never lost; collisions only enlarge the fibre.
      const seen4=new Uint8Array((prev.oldMats.length/4));
      const table4=new Uint32Array((prev.oldMats.length/4)*12);
      let ids=[];
      for(let u=0;u<n;u++){
        const m=prev.mi[u], p=prev.pi[u];
        if(m!==oldL||p!==oldR){
          oldL=m;oldR=p;ids=[];
          if(lev>1&&!seen4[p]){
            for(let i=0;i<12;i++)table4[12*p+i]=fingerprint(multiply(A4[i],get(prev.oldMats,p)));
            seen4[p]=1;
          }
          for(const A of A2){
            const B=multiply(A,get(prev.mats,m));
            if(B.every(x=>x%2===0))continue;
            if(lev>1){
              const h=fingerprint(B);
              let yes=false;
              for(let i=12*p;i<12*p+12;i++)if(table4[i]===h){yes=true;break;}
              // A hash collision can only retain an extra matrix.
              if(!yes)continue;
            }
            const j=T.insert(B);
            if(!ids.includes(j))ids.push(j);
          }
        }
        bi[u]=baseN;
        for(const j of ids){source[baseN]=u;baseM[baseN++]=j;}
      }
      bi[n]=baseN;
    }
    const counters=new Uint32Array(baseN);let todo=grow(Uint32Array);
    if(baseN*K>=2**32)throw Error("packed vertex identifier range");
    function enqueue(v,s){
      const b=1<<s;
      if((counters[v]&b)===0){counters[v]|=b;todo.add(v*K+s);}
    }
    const bp=new Uint32Array(baseN+1), gb=grow(Uint32Array), desc=grow(Uint16Array);
    {
      // Memoize a bounded number of matrix transitions; retain every edge found.
      const CT=1<<20,kc=new Uint32Array(CT),vc=new Float64Array(CT);
      function transition(m,a){
        const i=m*(C+1)+a+1;
        if(i>=2**32)throw Error("cache key");
        const k=(Math.imul(i,0x9e3779b1)>>>12)&(CT-1);
        if(kc[k]===i)return vc[k];
        const [M,w]=stepWord(T.read(m),0,a), j=T.lookup(swap(M));
        let ans=-1;
        if(j>=0&&w.every((v,k)=>k%2===0||v<=C)){
          let f=0;
          if(w.length)f=(w.length===2?1:2)|(w[0]<<2)|(w.at(-2)<<3)|(w[1]<<4)|(w.at(-1)<<8);
          ans=j*4096+f;
        }
        kc[k]=i;vc[k]=ans;
        return ans;
      }
      for(let b=0;b<baseN;b++){
        bp[b]=gb.length;
        const u=source[b], m=baseM[b];
        for(let e=prev.ep[u];e<prev.ep[u+1];e++){
          const a=prev.lab[e], v=prev.to[e], k=transition(m,a);if(k<0)continue;
          const j=Math.floor(k/4096), f=k%4096;
          for(let z=bi[v];z<bi[v+1];z++)if(baseM[z]===j){
            gb.add(z);desc.add((a<<12)|f);
            if(f&3)enqueue(z,((1-((f>>>3)&1))*C)+((f>>>8)&15)-1);
            break;
          }
        }
      }
      bp[baseN]=gb.length;
    }
    T.clear();global.gc?.();
    const be=gb.view(), de=desc.view();
    function follow(s,f){
      const kind=f&3;
      if(!kind)return s>=C?s-C:s+C;
      const p=s>=C?1:0, q=s%C+1;
      const first=(f>>>2)&1, r=((f>>>4)&15)+(first===p?q:0);
      if(r>C)return -1;
      const end=1-((f>>>3)&1);
      return end*C+(kind===1?r:((f>>>8)&15))-1;
    }
    for(let ix=0;ix<todo.length;ix++){
      if(ix>=maxStates)return {limited:true,base:baseN,states:todo.length};
      const h=todo.array[ix], b=Math.floor(h/K), s=h%K;
      for(let e=bp[b];e<bp[b+1];e++){const z=follow(s,de[e]);if(z>=0)enqueue(be[e],z);}
    }
    const offset=new Uint32Array(baseN+1);
    for(let i=0;i<baseN;i++)offset[i+1]=offset[i]+pop(counters[i]);
    const length=offset[baseN];
    if(length!==todo.length)throw Error("counter uniqueness");
    todo=null;global.gc?.();
    function num(b,s){const c=1<<s;if(!(counters[b]&c))throw Error("counter closure");return offset[b]+pop(counters[b]&(c-1));}
    const forward=grow(Uint32Array), edgeLabels=grow(Uint8Array), ep=new Uint32Array(length+1);
    let vertex=0;
    for(let b=0;b<baseN;b++){
      for(let mask=counters[b];mask;mask&=mask-1){
        const s=31-Math.clz32(mask&-mask);
        ep[vertex++]=forward.length;
        for(let e=bp[b];e<bp[b+1];e++){
          const z=follow(s,de[e]);
          if(z>=0){forward.add(num(be[e],z));edgeLabels.add(de[e]>>>12);}
        }
      }
    }
    ep[length]=forward.length;
    const to=forward.view(), labels=edgeLabels.view();
    const enter=new Int32Array(length), low=new Int32Array(length), comp=new Int32Array(length);
    comp.fill(-1); const stack=new Int32Array(length), dfs=new Int32Array(length), cur=new Uint32Array(length);
    let order=0,group=0,sp=0,hp=0;
    function push(i){
      enter[i]=low[i]=++order;stack[sp++]=i;dfs[hp]=i;cur[hp++]=ep[i];
    }
    for(let v=0;v<length;v++)if(!enter[v]){
      push(v);
      while(hp){
        const z=hp-1,u=dfs[z];
        if(cur[z]<ep[u+1]){
          const j=to[cur[z]++];
          if(!enter[j])push(j);
          else if(comp[j]<0&&enter[j]<low[u])low[u]=enter[j];
        } else {
          if(low[u]===enter[u]){
            let j;do{j=stack[--sp];comp[j]=group;}while(j!==u);group++;
          }
          if(--hp&&low[u]<low[dfs[hp-1]])low[dfs[hp-1]]=low[u];
        }
      }
    }
    const remap=new Int32Array(length), internal=new Uint32Array(length), groupSeen=new Uint8Array(group);
    remap.fill(-1);
    let kept=0, excess=0, ecount=0, ng=0;
    for(let v=0;v<length;v++){
      let i=0;
      for(let e=ep[v];e<ep[v+1];e++){
        if(comp[v]<comp[to[e]])throw Error("non-monotone component certificate");
        if(comp[v]===comp[to[e]])i++;
      }
      if(i){
        remap[v]=kept++;internal[v]=i;excess+=i-1;ecount+=i;
        if(!groupSeen[comp[v]]){groupSeen[comp[v]]=1;ng++;}
      }
    }
    const newM=grow(lev<32?Uint32Array:Float64Array), oldM=grow(lev<=32?Uint32Array:Float64Array);
    const H={mats:null,oldMats:null,mi:new Uint32Array(kept),pi:new Uint32Array(kept),
             ep:new Uint32Array(kept+1),
             to:new Uint32Array(ecount),lab:new Uint8Array(ecount)};
    const aMap=new Int32Array(T.size),bMap=new Int32Array(prev.mats.length/4);
    aMap.fill(-1);bMap.fill(-1);
    let at=0;
    for(let b=0;b<baseN;b++){
      for(let i=offset[b];i<offset[b+1];i++){
        if(!internal[i])continue;
        const j=remap[i], m=baseM[b], u=source[b], mm=prev.mi[u];
        if(aMap[m]<0){aMap[m]=newM.length/4;for(const x of T.read(m))newM.add(x);}
        if(bMap[mm]<0){bMap[mm]=oldM.length/4;for(const x of get(prev.mats,mm))oldM.add(x);}
        H.mi[j]=aMap[m];H.pi[j]=bMap[mm];H.ep[j]=at;
        for(let e=ep[i];e<ep[i+1];e++)if(comp[i]===comp[to[e]]){
          H.to[at]=remap[to[e]];H.lab[at++]=labels[e];
        }
      }
    }
    H.ep[kept]=at;H.mats=newM.view();H.oldMats=oldM.view();
    if(at!==ecount)throw Error("SCC edge count");
    return {G:H,base:baseN,states:length,retained:kept,excess,cyclicSccs:ng,edges:ecount,uniqueMatrices:H.mats.length/4};
  }
  const log=[];
  for(let lev=1;lev<=maxDepth;lev++){
    const {G:H,...r}=advance(G,lev);G=H;global.gc?.();
    const row={C,level:lev,...r};log.push(row);report(row);
    if(r.limited || r.excess===0)return {closed:!r.limited,log};
  }
  return {closed:false,log};
}
const c=Number(process.argv[2]||12), d=Number(process.argv[3]||44), lim=Number(process.argv[4]||8000000);
const z=boundedDoubling(c,d,lim,row=>console.log(JSON.stringify(row)));
const last=z.log.at(-1), peak=Math.max(...z.log.map(r=>r.states));
if(c===12&&d>=41&&lim>3248245){
  if(!z.closed||last.level!==41||last.retained!==23464||last.edges!==23464||last.excess!==0||peak!==3248245)
    throw Error("C=12 certificate mismatch");
}
console.log(JSON.stringify({finished:true,closed:z.closed,last,peak}));
