#!/usr/bin/env python3
"""Independent exact replay of exceptional punctured ADE equator classification.

Run: python3 kissing_ade_independent_exact_audit.py
For a quick run: python3 kissing_ade_independent_exact_audit.py --quick
Requires Python 3.9+ and Node.js 18+, with no packages or data files.
The full replay scans every point of the relevant Weyl orbits, without
pruning by angle. The quick replay retains the exact chamber closures
in all ranks and skips only the E8 full angle and mask orbit pass.
"""

from fractions import Fraction
from math import lcm
from itertools import combinations,product
import argparse
import json
import subprocess

if not __debug__:
    raise RuntimeError('Run without -O to keep exact checks enabled')

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def unit(i,x): return tuple(x if j==i else 0 for j in range(8))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def det(A):
    # Bareiss determinant with exact division, without row normalization.
    T=[list(r) for r in A];n=len(T);sgn=1;prev=1
    if not n:return 1
    for k in range(n-1):
        i=next((i for i in range(k,n) if T[i][k]),None)
        if i is None:return 0
        if i!=k:T[i],T[k]=T[k],T[i];sgn=-sgn
        pivot=T[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=T[i][j]*pivot-T[i][k]*T[k][j]
                assert numerator%prev==0
                T[i][j]=numerator//prev
            T[i][k]=0
        prev=pivot
    return sgn*T[-1][-1]

def solve(A,b):
    d=det(A)
    if not d:return None
    return tuple(Fraction(det([r[:i]+[t]+r[i+1:] for r,t in zip(A,b)]),d)
                 for i in range(len(A)))

E8=[add(unit(i,a),unit(j,b)) for i,j in combinations(range(8),2) for a,b in product((-2,2),repeat=2)]
E8 += [w for w in product((-1,1),repeat=8) if w.count(-1)%2==0]
assert len(set(E8))==240
chain=[(1,-1,-1,-1,-1,-1,-1,1)]+[add(unit(i,-2),unit(i+1,2)) for i in range(6)]
extra=add(unit(0,2),unit(1,2))

def data(n):
    A=chain[:n-1]+[extra]
    assert all(dot(x,y)%4==0 for x in A for y in A)
    G=[[dot(x,y)//4 for y in A]for x in A]
    inv=[solve(G,[int(i==j) for j in range(n)])for i in range(n)]
    def dual(y):return tuple(dot(row,y)for row in inv)
    def physical(c):return tuple(dot(z,c) for z in zip(*A))
    RR=[]
    for r in E8:
        assert all(dot(a,r)%4==0 for a in A)
        c=dual(tuple(dot(a,r)//4 for a in A))
        if physical(c)==r:
            assert all(t.denominator==1 for t in c)
            RR.append((tuple(map(int,c)),r))
    RR.sort()
    R=[c for c,r in RR]
    assert len(R)=={6:72,7:126,8:240}[n]
    P=[r for r in R if min(r)>=0]
    def norm(y):return dot(y,dual(y))
    eqroots={tuple(dot(x,r)//4 for x in A)for c,r in RR}
    top={p:{q for q in P if p!=q and all(u<=v for u,v in zip(p,q))}for p in P}
    def verts(C):
        return {
          tuple(x[js.index(i)] if i in js else Fraction(0) for i in range(n))
          for z in range(min(n,len(C))+1)
          for js in combinations(range(n),z)
          for qs in combinations(C,z)
          for x in [solve([[q[j]for j in js]for q in qs],[1]*z)]
          if x is not None and all(t>=0 for t in x)
          and all(sum(q[j]*v for j,v in zip(js,x))<=1 for q in C)
        }
    # Cramer's rule for size zero is the empty tuple, hence includes origin.
    todo=[frozenset()];opened=set(todo);clean=[];front=[]
    gen=set()
    for m in todo:
        C=[r for r in P if r not in m and top[r]<=m]
        if all(any(q[i]>0 for q in C)for i in range(n)):
            V=verts(C)
            if all((norm(y)<2) or (norm(y)==2 and y in eqroots)for y in V):
                clean.append(m);gen.update(V)
                for q in C:
                    new=m|{q}
                    if new not in opened:opened.add(new);todo.append(new)
                continue
        front.append(m)
    high=[]
    for I in front:
        C=[r for r in P if r not in I and top[r]<=I]
        if all(any(q[i]>0 for q in C)for i in range(n)):
            W=verts(C)
            high.append((len(I),str(max(map(norm,W))),sum(norm(y)==2 and y not in eqroots for y in W)))
        else:high.append((len(I),'unbounded',None))
    scale=lcm(*(z.denominator for y in gen for z in physical(dual(y))))
    V=sorted({tuple(int(z*scale)for z in physical(dual(y)))for y in gen})
    if n==6:
        pairs=[(a,b)for a,b in combinations(R,2)if tuple(x+y for x,y in zip(a,b))==(1,0,0,0,0,0)]
        def ax(r):return min(r,tuple(-x for x in r))
        assert len(pairs)==10 and len({ax(t)for p in pairs for t in p})==20
    return dict(n=n,roots=RR,facets=A,V=V,scale=scale,front=[sorted(m)for m in front],
                count=[len(todo),len(clean),len(front),len(gen)],profile=high,
                radius=str(max(map(norm,verts([max(P,key=sum)])))))


NODE = r'''
"use strict";
const assert=require("node:assert/strict");
const fs=require('node:fs');
const data=JSON.parse(fs.readFileSync(0,'utf8'));
const dot=(u,v)=>u[0]*v[0]+u[1]*v[1]+u[2]*v[2]+u[3]*v[3]+u[4]*v[4]+u[5]*v[5]+u[6]*v[6]+u[7]*v[7];
const re=(v,r)=>{
 const q=dot(v,r)/4;
 if(!q)return v;
 assert(Number.isInteger(q));
 return v.map((x,j)=>x-q*r[j]);
};
const key=x=>x.join(",");
const smaller=(x,y)=>x.every((u,j)=>u<=y[j]);
const sort=(x)=>x.sort((a,b)=>a-b);
for(const s of data){
  const {n,roots,facets,V,scale,front,count,radius}=s;
  assert.deepEqual(count,{6:[12,7,5,12],7:[13,9,4,15],8:[19,13,6,20]}[n]);
  assert.equal(radius,{6:"4/3",7:"3/2",8:"1"}[n]);
  const ix=new Map(roots.map(([r],j)=>[key(r),j]));
  const ja=new Map(roots.map(([,r],j)=>[key(r),j]));
  const Neg=roots.map(([a])=>ix.get(key(a.map(x=>-x))));
  const physical=roots.map(([,a])=>a);
  const shift=facets.map(r=>physical.map(x=>ja.get(key(re(x,r)))));
  if(n===6)shift.push(roots.map(([q])=>ix.get(key([q[4],q[3],q[2],q[1],q[0],q[5]]))));
  assert(shift.every(row=>new Set(row).size===roots.length));
  const D=4*scale*scale;
  const ns=V.map(v=>dot(v,v));
  const vv=V.map((v,i)=>[v,ns[i]]).filter(([,a])=>2*a>3*D&&a<2*D);
  const mask=(v)=>physical.flatMap((r,i)=>dot(r,v)>4*scale?[i]:[]);
  const high=vv.map(([v,a])=>[v,a,mask(v),[]]);
  for(const z of high)z[3]=new Set(z[2].map(i=>Neg[i]));
  let num=0,raw=0,orbitSizes=[], interior=new Set();
  for(let j=0;j<V.length;++j){
   if(ns[j]>=2*D)continue;
   const start=V[j], orbit=[start], seen=new Set([key(start)]), hW=2*D-ns[j];
   for(const w of orbit){
    let m=null;
    for(const [v,a,B,op]of high){
      const d=dot(v,w);
      if(d>=-D||(d+D)**2<=(2*D-a)*hW)continue;
      ++num;
      if(!m)m=mask(w);
      if(m.some(i=>op.has(i)))continue;
      interior.add(key(sort([...new Set(B.concat(m))])));
    }
    for(const r of facets){
      const z=re(w,r);
      if(z===w)continue;
      const k=key(z);
      if(!seen.has(k)){seen.add(k);orbit.push(z);}
    }
   }
   raw+=orbit.length;
   orbitSizes.push(orbit.length);
  }
  assert.equal(raw,{6:6319,7:126507,8:5631841}[n]);
  assert.equal(num,{6:210,7:4151,8:24106}[n]);
  assert.equal(interior.size,{6:4,7:0,8:0}[n]);
  const prototypes={6:["012211","112111"],7:["1232112","1222211"],8:["13543213","23432212"]}[n]
    .map(s=>roots.flatMap(([r],i)=>smaller(Array.from(s,Number),r)?[i]:[]));
  if(n===6)prototypes.push(sort("-122111 -112111 -111111 -111110 112211 122211 123211 123212".split(" ")
    .map(s=>ix.get(key(Array.from(s.replace("-",""),x=>(s[0]==="-"?-1:1)*Number(x)))))));
  const orbitsets=prototypes.map(m=>{
    const q=[m],found=new Set([key(m)]);
    for(const a of q)for(const g of shift){
       const r=sort(a.map(i=>g[i])),u=key(r);
       if(!found.has(u)){found.add(u);q.push(r);}
    }
    return found;
  });
  const sizes=orbitsets.map(x=>x.size);
  assert.deepEqual(sizes,{6:[432,6480,2160],7:[4032,30240],8:[17280,181440]}[n]);
  function dominates(m,S,k){
    if(m.length<k)return false;
    const stack=[];
    function go(l){
     if(stack.length===k)return S.has(key(stack));
     for(let j=l;j<=m.length-(k-stack.length);++j){
       stack.push(m[j]);
       if(go(j+1))return true;
       stack.pop();
     }
     return false;
    }
    return go(0);
  }
  const ext=front.map(r=>sort(r.map(x=>ix.get(key(x)))));
  for(const m of ext)assert(orbitsets.slice(0,2).some((o,j)=>dominates(m,o,prototypes[j].length)));
  for(let j=0;j<2;++j)assert(ext.some(m=>orbitsets[j].has(key(m))));
  for(const m of interior)assert(orbitsets.some((o,j)=>dominates(m.split(",").map(Number),o,prototypes[j].length)));
  if(n===6)assert([...interior].some(m=>orbitsets[2].has(m)));
  for(const [i,m]of prototypes.entries()){
    assert(!m.some(x=>m.includes(Neg[x])));
    for(const [j,S]of orbitsets.entries())if(i!==j)assert(!dominates(m,S,prototypes[j].length));
  }
  console.log(JSON.stringify({n,count,radius,profile:s.profile,fullOrbitSum:raw,orbitSizes,badPairs:num,interiorMasks:interior.size,maskOrbitSizes:sizes,pass:true}));
}

'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    d = [data(n) for n in (6,7,8)]
    assert [t['count'] for t in d]==[[12,7,5,12],[13,9,4,15],[19,13,6,20]]
    assert [t['radius'] for t in d]==['4/3','3/2','1']
    assert [t['profile'] for t in d]==[
        [(5,'10/3',0),(5,'10/3',0),(6,'10/3',0),(6,'2',1),(6,'10/3',0)],
        [(6,'2',1),(7,'2',1),(8,'2',1),(8,'2',1)],
        [(8,'2',1),(9,'2',1),(10,'2',1),(11,'2',1),(12,'2',1),(12,'2',1)],
    ]
    print("Exact chamber inventories E6/E7/E8 validated", flush=True)
    subprocess.run(["node", "-e", NODE], check=True, text=True,
                   input=json.dumps(d[:2] if args.quick else d, separators=(",",":")))
    if args.quick:
        print("Quick replay: E8 full orbit pass was not requested")

if __name__ == "__main__":
    main()
