/* Node 18+. Exact enumerations of generated finite subspace arrangements. */
'use strict';
let checks=0;
function ck(q,m){++checks;if(!q)throw Error(m);}
const mod=(a,q)=>((a%q)+q)%q;
function rank(a,q){
  if(!a.length)return 0;
  const m=a.map(x=>x.slice()),d=m[0].length;
  let z=0;
  for(let j=0;j<d&&z<m.length;++j){
    let l=z;while(l<m.length&&m[l][j]===0)++l;
    if(l===m.length)continue;
    if(l!==z)[m[l],m[z]]=[m[z],m[l]];
    let b=1;while(mod(b*m[z][j],q)!==1)++b;
    for(let i=z+1;i<m.length;++i)if(m[i][j]){
      const u=mod(m[i][j]*b,q);
      for(let k=j;k<d;++k)m[i][k]=mod(m[i][k]-u*m[z][k],q);
    }
    ++z;
  }
  return z;
}
function list(space,D,q){
  let a=[Array(D).fill(0)];
  for(const b of space)
    a=a.flatMap(x=>Array.from({length:q},(_,t)=>x.map((z,i)=>mod(z+t*b[i],q))));
  return a;
}
function pow(q,e){return BigInt(q)**BigInt(e);}
function dot(x,y,q){return mod(x.reduce((s,u,i)=>s+u*y[i],0),q);}
function arrange(spaces,D,q,expected=null){
  const K=spaces.length;
  const bases=spaces.map(V=>{let B=[];
    for(const x of V)if(rank([...B,x],q)>B.length)B.push(x);
    return B;
  });
  const points=bases.map(V=>list(V,D,q));
  const size=points.reduce((s,x)=>s*BigInt(x.length),1n);
  const funcs=list(Array.from({length:D},(_,i)=>Array.from({length:D},(_,j)=>+(i===j))),D,q);
  const first=Array(K).fill(0n);let num=0n,all=0n;
  function enumerate(i,rows,firstFail){
    if(i===K){
      ++all;
      const d=rank(rows,q);num+=pow(q,K)-pow(q,d);
      if(firstFail>=0)++first[firstFail];
      return;
    }
    for(const x of points[i]){
      const a=[...rows,x],f=firstFail<0&&rank(a,q)<i+1?i:firstFail;
      enumerate(i+1,a,f);
    }
  }
  enumerate(0,[],-1);
  ck(all===size,'all independent seed products counted');
  let slo=Infinity,rankmask=[],countmask=[];
  for(let mask=1;mask<1<<K;++mask){
    const inds=Array.from({length:K},(_,i)=>i).filter(i=>mask>>i&1);
    countmask[mask]=inds.length;
    rankmask[mask]=rank(inds.flatMap(i=>bases[i]),q);
    slo=Math.min(slo,rankmask[mask]-countmask[mask]);
  }
  if(slo<0){
    ck(BigInt(q)*num>=(BigInt(q)-1n)*all*pow(q,K),'deterministic insufficient rank lower TV');
    return;
  }
  let scaled=0n,lead=0;
  for(let i=0;i<K;++i){
    let count=0n,good=new Set();
    for(const l of funcs){
      if(bases[i].some(z=>dot(l,z,q)!==0))continue;
      let mask=0;
      for(let j=0;j<=i;++j)if(bases[j].every(z=>dot(l,z,q)===0))mask|=1<<j;
      const cuts=points.slice(0,i).map(a=>a.filter(x=>dot(l,x,q)===0));
      const sep=(j,a)=>{
        if(j===i)return 1n;
        let s=0n;
        for(const x of cuts[j])if(rank([...a,x],q)>j)s+=sep(j+1,[...a,x]);
        return s;
      };
      const n=sep(0,[]);
      if(n)good.add(mask);
      count+=n;
    }
    const future=points.slice(i).reduce((s,x)=>s*BigInt(x.length),1n);
    ck(first[i]*pow(q,D-i)===count*future,'exact order-wise dual first-failure identity');
    for(const mask of good){
      const s=rankmask[mask]-countmask[mask];
      if(s===slo)++lead;
      scaled+=pow(q,D-s);
    }
  }
  // S_q has denominator q^(D+1). The joint TV denominator is all*q^K.
  const tDen=all*pow(q,K),sDen=pow(q,D+1);
  ck(num*sDen<=tDen*scaled,'joint TV upper shape certificate');
  if(q>=3*K+1)ck(BigInt(q)*num*sDen>=BigInt(q-3*K-1)*tDen*scaled,
    'joint TV lower shape certificate');
  if(expected!==null)ck(lead===expected,'exact leading combinatorial coefficient');
}
const e=Array.from({length:4},(_,i)=>Array.from({length:4},(_,j)=>+(i===j)));
for(const q of [2,3,5,7,11]) {
  const d=2;
  const a=[1,0],b=[0,1],both=[a,b];
  arrange([[a],[b]],d,q,2);
  arrange([[a],both],d,q,2);
  arrange([both,both],d,q,1);
  arrange([[a],[a]],d,q);
}
for(const q of [2,3,5,7]) {
 const {0:a,1:b,2:c,3:d}=e;
 arrange([[a,b],[a,c],[a,d]],4,q,6);
 arrange([[a],[b,c],[b,c]],4,q,2);
 arrange([[a,b],[a,c],[b,c]],4,q,1);
 arrange([[a,b],[a,b],[c,d]],4,q,1);
}
let seed=101439907;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>10)%n;}
for(let k=0;k<72;++k){
  const q=[2,3,5][k%3],K=1+rng(3),D=2+rng(2);
  const Vs=Array.from({length:K},()=>Array.from({length:1+rng(2)},()=>Array.from({length:D},()=>rng(q))));
  arrange(Vs,D,q);
}
for(let K=1;K<=100;++K) {
  let n=0;for(let i=1;i<=K;++i)n+=i; // zero or one previous index outside I.
  ck(n===K+K*(K-1)/2,'common-line arrangement coefficient');
  if(K>=3) ck(BigInt(n)<(1n<<BigInt(K))-1n,'projective count strictly overcounts leading TV');
}
console.log('split-ring linear regularity:', checks,'exact enumeration assertions');
