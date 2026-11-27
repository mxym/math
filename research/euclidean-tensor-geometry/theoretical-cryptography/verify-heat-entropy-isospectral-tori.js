'use strict';
const assert = require('node:assert/strict');
let checks=0, operations=0;
function eq(x,y){assert.deepEqual(x,y);checks++;}
const zeros=n=>Array(n).fill(0);
function roots(n,spin=false){
  const R=[];
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)for(const s of [-2,2])for(const t of [-2,2]){
    const v=zeros(n);v[i]=s;v[j]=t;R.push(v);
  }
  if(spin)for(let k=0;k<1<<n;k++){
    const v=Array.from({length:n},(_,i)=>((k>>i)&1)?1:-1);
    if(v.filter(x=>x<0).length%2===0)R.push(v);
  }
  return R;
}
const sum=(x,y)=>x.map((u,j)=>u+y[j]), sub=(x,y)=>x.map((u,j)=>u-y[j]), key=x=>x.join(',');
function group(R,spin){
  const P=new Map(), G=new Map(), n=R[0].length;
  for(const v of R)for(const w of R){
    const s=sum(v,w),k=key(s);
    if(!P.has(k))P.set(k,{s,p:0});
    P.get(k).p++;operations++;
  }
  for(const {s,p} of P.values()){
    const a=s.map(Math.abs).filter(Boolean).sort((u,v)=>u-v);
    const k=key(a)+(spin&&a.length===n?';'+s.filter(x=>x<0).length%2:'');
    if(!G.has(k)){
      let b=0;for(const v of R){b+=P.get(key(sub(s,v)))?.p??0;operations++;}
      G.set(k,[0,p,b]);
    }
    const row=G.get(k);eq(row[1],p);row[0]++;
  }
  return Object.fromEntries(G);
}
const E=roots(8,true),D=roots(16);
eq(E.length,240);eq(D.length,480);
const e=group(E,true), d=group(D,false);
eq(e,{
  '':[1,240,13440], '4':[16,14,1848], '4,4':[112,1,168], '2,2':[112,56,5253],
  '2,2,4':[1344,2,600], '2,2,2,2':[1120,14,1848], '2,2,2,2,2,2':[1792,2,600],
  '2,2,2,2,2,2,2,2;0':[128,1,168], '1,1,1,1,1,1,1,1;0':[128,56,5253],
  '1,1,1,1,1,1,1,3;1':[1024,14,1848], '1,1,1,1,1,1,3,3;0':[3584,2,600]
});
eq(d,{'':[1,480,26880], '4':[32,30,2520], '4,4':[480,1,168],
  '2,2':[480,56,5973], '2,2,4':[13440,2,408], '2,2,2,2':[29120,6,936]});
const five=G=>Object.values(G).reduce((s,[n,p,b])=>s+n*p*b,0);
eq(five(e),137813760);eq(five(d),350461440);
const E2=E.flatMap(v=>[v.concat(zeros(8)),zeros(8).concat(v)]);
// Different implementation, all 480 roots and all pair sums, with no orbit
// grouping. Each component of s minus a root lies between -6 and 6, and
// radix 17 gives an injective balanced integer encoding there.
function direct(R){
  const pow=Array.from({length:16},(_,i)=>17n**BigInt(i));
  const A=R.map(v=>v.reduce((s,x,i)=>s+BigInt(x)*pow[i],0n));
  const P=new Map();
  for(const v of A)for(const w of A){const s=v+w;P.set(s,(P.get(s)??0)+1);operations++;}
  let c3=0,c4=0,c5=0;
  for(const x of A)c3+=P.get(x)??0;
  for(const [s,p] of P){c4+=p*p;let b=0;for(const r of A){b+=P.get(s-r)??0;operations++;}c5+=p*b;}
  return [P.size,c3,c4,c5];
}
eq(direct(E2),[76321,26880,2867040,340139520]);
eq(direct(D),[43553,26880,2867040,350461440]);
eq(2*five(e)+20*240*e[''][2],340139520);
eq((five(d)-340139520)/120,86016);
const Q=([a,b,c,d])=>10*(a*a+b*b+c*c+d*d)+2*(a*b-c*d)+4*(a*c-b*d)+6*(a*d-b*c);
function tetra(sgn){
  const A=[], U=new Map(), B=86;
  for(let x=-4;x<=4;x++)for(let y=-4;y<=4;y++)for(let z=-4;z<=4;z++)for(let w=-4;w<=4;w++){
    if((z+x-y)%3||(w-sgn*(x+y))%3)continue;
    const v=[x,y,z,w],q=Q(v);
    if(q>0&&q<=B){A.push([v,q]);U.set(key(v),q);}
  }
  const mn=Math.min(...U.values());eq(mn,18);
  const H=Array(B+1).fill(0),K=Array(B+1).fill(0),P=new Map(),tri=[];
  for(const [v,g] of A)for(const [w,h] of A){
    if(g+h+mn>B)continue;
    const s=sum(v,w),k=key(s),q=U.get(k);operations++;
    if(q&&g+h+q<=B){
      H[g+h+q]++;
      if(g+h+q===B)tri.push([g,h,q].sort((a,b)=>a-b));
    }
    if(g+h+2*mn<=B){
      if(!P.has(k))P.set(k,new Map());
      const D=P.get(k);D.set(g+h,(D.get(g+h)??0)+1);
    }
  }
  for(const D of P.values())for(const [g,x] of D)for(const [h,y] of D)if(g+h<=B){K[g+h]+=x*y;operations++;}
  return [H,K,tri];
}
const [H,K,tr]=tetra(-1),[Hp,Kp,trp]=tetra(1);
eq(H.slice(0,86),Hp.slice(0,86)); eq(K,Kp); eq([H[86],Hp[86]],[12,0]);
eq(tr,Array.from({length:12},()=>[18,30,38]));eq(trp,[]);
console.log('PASS',checks,'assertions over',operations,'exact pair/convolution operations');
