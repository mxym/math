"""Conway rank-42 two-type seven-overlap core: exact Python 3.10+ verifier.
Run alongside seven-overlap-certificates-{a,b}.json. No optimizer or floating arithmetic.
Optional chart labels: python3 seven-overlap-core.py 10 11
"""
from itertools import combinations, product,permutations
from collections import Counter
def panels(h):
 X=tuple(range(5)); ps=list(combinations(X,2)); A=(0,1,2); B=(0,3,4) if h==1 else (0,1,3); caps=[2-(i in A and j in A)-(i in B and j in B) for i,j in ps];inc=[4-(i in A)-(i in B) for i in X]
 perms=[tuple(ps.index(tuple(sorted((u[i],u[j])))) for i,j in ps) for u in permutations(X) if {frozenset(u[i] for i in s) for s in [A,B]}=={frozenset(A),frozenset(B)}]
 panels=[]
 for b in product(*(range(c+1) for c in caps)):
  if any(sum(b[k] for k,p in enumerate(ps) if i in p)!=v for i,v in enumerate(inc)):continue
  c=tuple(k-j for k,j in zip(caps,b))
  imgs=[tuple(w[k] for k in perm) for w in (b,c) for perm in perms]
  if b==min(imgs):panels.append((b,c))
 print(h,'chart orbits',len(panels),'autA',len(perms))
 return panels
from collections import defaultdict
def configs(h,b):
 ps=list(combinations(range(5),2));A=[frozenset(ps[k]) for k,n in enumerate(b) for _ in range(n)]
 T=(frozenset([0,1,2]),frozenset([0,3,4]) if h==1 else frozenset([0,1,3]))
 W=list(combinations(range(4),2));wm=[(1<<a)|(1<<z) for a,z in W]
 # Normalize the B' vertex chosen by each ordered A' neighbor. Other B' labels can still swap.
 for aa in ((0,0),(0,1)):
  if h+(aa[0]==aa[1])>2:continue
  Auto=[z for z in permutations(range(4)) if z[aa[0]]==aa[0] and z[aa[1]]==aa[1]];maps=[[wm.index((1<<z[j])|(1<<z[k])) for j,k in W] for z in Auto]
  quotas=[4-aa.count(i) for i in range(4)]
  cand=[[k for k,w in enumerate(wm) if all(len(a&t)+((w>>z)&1)<=2 for t,z in zip(T,aa))] for a in A]
  def walk(i,S,r):
   if i==7:
    if r!=quotas:return
    # All A_i against B'_j: number of common neighbors through B plus A'.
    if any(sum(l in A[k] and ((wm[v]>>j)&1) for k,v in enumerate(S))+sum(l in t and z==j for t,z in zip(T,aa))>2 for l in range(5) for j in range(4)):return
    # identical A-pair B rows can be permuted. Apply the residual color permutations on B'.
    def norm(t):
     out=[]; j=0
     while j<len(A):
      k=j+1
      while k<len(A) and A[k]==A[j]:k+=1
      out.extend(sorted(t[j:k]));j=k
     return tuple(out)
    if tuple(S)!=min(norm([sigma[v] for v in S]) for sigma in maps):return
    yield tuple(wm[x] for x in S),aa
    return
   for v in cand[i]:
    w=wm[v]
    if S.count(v)>=2:continue
    if i and A[i]==A[i-1] and S[-1]>v:continue
    if any((w&wm[u]).bit_count()+len(A[j]&A[i])>2 for j,u in enumerate(S)):continue
    nr=[x+((w>>j)&1) for j,x in enumerate(r)]
    if any(k>t or k+(6-i)<t for k,t in zip(nr,quotas)):continue
    yield from walk(i+1,S+[v],nr)
  yield from walk(0,[],[0]*4)
from time import time
ps=list(combinations(range(5),2)); pairs7=list(combinations(range(7),2))
def allcores(h,bc,cc,Bconf,Cconf):
 T=([0,1,2],[0,3,4] if h==1 else [0,1,3]); W,ab=Bconf; V,ac=Cconf
 if h+(ab[0]==ab[1])+(ac[0]==ac[1])>2:return
 ba=[ps[k] for k,n in enumerate(bc) for _ in range(n)];ca=[ps[k] for k,n in enumerate(cc) for _ in range(n)]
 z=[0]*29
 def add(i,j):z[i]|=1<<j;z[j]|=1<<i
 def rem(i,j):z[i]^=1<<j;z[j]^=1<<i
 for j,t in enumerate(T):
  for i in t:add(i,5+j)
  add(5+j,14+ab[j]);add(5+j,25+ac[j])
 for i,(g,w) in enumerate(zip(ba,W)):
  for a in g:add(a,7+i)
  for j in range(4):
   if (w>>j)&1:add(7+i,14+j)
 for i,(g,v) in enumerate(zip(ca,V)):
  for a in g:add(a,18+i)
  for j in range(4):
   if (v>>j)&1:add(18+i,25+j)
 def ok(i,j):
  return (z[i]&z[j]).bit_count()+(z[i]>>j&1)<=2
 def edgeok(i,j):
  if (z[i]&z[j]).bit_count()>1:return False
  for m,v in [(z[i],j),(z[j],i)]:
   while m:
    u=m&-m;m-=u;k=u.bit_length()-1
    if (z[k]&z[v]).bit_count()+((z[k]>>v)&1)>=2:return False
  return True
 for mat in {tuple(sorted(zip(ab,ac))),tuple(sorted(zip(ab,ac[::-1])))}:
  if mat[0]==mat[1]:continue
  for i,j in mat:add(14+i,25+j)
  if all(ok(i,j) for i,j in combinations(range(29),2)):
   options=[]
   for i in range(7):
    a=18+i;opts=[]
    for j,k in pairs7:
     j+=7;k+=7
     if not edgeok(a,j):continue
     add(a,j)
     if edgeok(a,k):opts.append((j,k))
     rem(a,j)
    options.append(opts)
   order=sorted(range(7),key=lambda i:len(options[i]))
   deg=[0]*14
   def walk(st):
    if st==7:
     yield tuple(z)
     return
    i=order[st];v=18+i
    for j,k in options[i]:
     if deg[j]>=2 or deg[k]>=2:continue
     if not edgeok(v,j):continue
     add(v,j)
     if edgeok(v,k):
      add(v,k);deg[j]+=1;deg[k]+=1;yield from walk(st+1);deg[j]-=1;deg[k]-=1;rem(v,k)
     rem(v,j)
   yield from walk(0)
  for i,j in mat:rem(14+i,25+j)
def canonical(z):
 n=len(z);init=((tuple(range(0,5)),tuple(range(5,7)),tuple(range(7,14)),tuple(range(14,18)),tuple(range(18,25)),tuple(range(25,29))))
 def rec(part):
  while True:
   masks=[sum(1<<j for j in c) for c in part];new=[]
   for cell in part:
    if len(cell)==1:new.append(cell);continue
    a={}
    for i in cell:
     k=tuple((z[i]&m).bit_count() for m in masks);a.setdefault(k,[]).append(i)
    new.extend(tuple(a[t]) for t in sorted(a))
   if len(new)==len(part):break
   part=tuple(new)
  c=min((v for v in part if len(v)>1),key=len,default=None)
  if c:
   i=part.index(c);return min(rec(part[:i]+((j,),tuple(k for k in c if k!=j))+part[i+1:]) for j in c)
  o=[s[0] for s in part];return tuple(sum(((z[i]>>j)&1)<<k for k,j in enumerate(o)) for i in o)
 a0=rec(init);a1=rec(init[:2]+init[4:]+init[2:4]);return min(a0,a1)
def cstats(h,c):
 bc,cc=panels(h)[c];bcf=list(configs(h,bc));ccf=list(configs(h,cc));ct=0;seen={}
 for li,b in enumerate(bcf):
  for ri,y in enumerate(ccf):
   for zi,z in enumerate(allcores(h,bc,cc,b,y)):
    ct+=1;k=canonical(z)
    if k not in seen:seen[k]=(li,ri,zi,z)
 return ct,seen
import base64
import hashlib
import itertools
import json
import sys
import zlib
from pathlib import Path
CELLS=[(0,1)]*5+[(1,0)]*2+[(1,2)]*7+[(2,1)]*4+[(2,0)]*7+[(0,2)]*4

def resid(z,i,j):
    return (12 if i==j else 0)+2-((z[i]>>j)&1)-(z[i]&z[j]).bit_count()

def words(z,R):
    co=[sum(1<<j for j in range(i+1,29) if R[i][j]) for i in range(29)]
    closed=[u|(1<<i) for i,u in enumerate(z)]
    tail=[0,0,0];head=[0,0,0];caps=[3,3,4];out=[]
    def rec(mask,opts):
        if tail==head:out.append(mask)
        while opts:
            u=opts&-opts;opts-=u;j=u.bit_length()-1;a,b=CELLS[j]
            if tail[a]>=caps[a] or head[b]>=caps[b]:continue
            new=mask|u
            if any((new&x).bit_count()>2 for x in closed if x&u):continue
            tail[a]+=1;head[b]+=1
            rec(new,opts&co[j])
            tail[a]-=1;head[b]-=1
    rec(0,(1<<29)-1)
    return out

def makecols(z,R,W,full):
    pairs=[(i,j) for i,j in itertools.combinations_with_replacement(range(29),2) if R[i][j]]
    loc={p:i+1 for i,p in enumerate(pairs)}
    sets=[[i for i in range(29) if w>>i&1] for w in W]
    b=[70]+[R[i][j] for i,j in pairs];e=len(b)
    col=[[0]+[loc[p] for p in itertools.combinations_with_replacement(ar,2)] for ar in sets]
    if full:
        ts=sorted(set(t for ar in sets for t in combinations(ar,3)))
        tl={t:e+j for j,t in enumerate(ts)}
        b.extend([1]*len(ts))
        for c,ar in zip(col,sets):
            c.extend(tl[t] for t in combinations(ar,3))
        for f,cap in enumerate([3,3,4]):
            mask=sum(1<<i for i,(u,t) in enumerate(CELLS) if u==f)
            inner=sum((z[k]&mask).bit_count()==cap for k,(u,t) in enumerate(CELLS) if f not in (u,t))
            for c,w in zip(col,W):
                if (w&mask).bit_count()==cap:c.append(len(b))
            b.append(1-inner)
    return col,b,e

def weights(s,b,e):
    out=[0]*len(b);seen=set()
    for i,n in s:
        assert isinstance(i,int) and isinstance(n,int) and 0<=i<len(b) and i not in seen
        assert i<e or n>=0
        seen.add(i);out[i]=n
    return out

def verifyone(z,rec):
    R=[[resid(z,i,j) for j in range(29)] for i in range(29)]
    assert all(n>=0 for row in R for n in row)
    kind,x=rec
    if kind=='n':
        assert len(x)==29 and all(isinstance(n,int) for n in x)
        assert sum(a*b*c for a,row in zip(x,R) for b,c in zip(x,row))<0
        return 0
    W=words(z,R)
    col,b,e=makecols(z,R,W,kind=='t')
    if kind=='m':
        assert 0<=x<e and b[x]>0 and not any(x in c for c in col)
        return 0
    if kind=='f':
        co=weights(x,b,e)
        assert sum(a*d for a,d in zip(co,b))<0
        assert all(sum(co[i] for i in c)>=0 for c in col)
        return 0
    assert kind=='t'
    lo=[0]*len(W);hi=[70 if not w else 2 if w.bit_count()==2 else 1 for w in W]
    assert all(not w or w.bit_count()>=2 for w in W)
    def walk(t):
        if t[0]=='f':
            assert len(t)==2
            co=weights(t[1],b,e)
            lam=[sum(co[i] for i in c) for c in col]
            assert sum(a*d for a,d in zip(co,b)) < sum(v*(lo[i] if v>=0 else hi[i]) for i,v in enumerate(lam))
            return 1
        kind,i,m,l,r=t
        assert kind=='b' and isinstance(i,int) and 0<=i<len(W) and isinstance(m,int) and lo[i]<=m<hi[i]
        a,u=lo[i],hi[i];hi[i]=m;lc=walk(l);hi[i]=u;lo[i]=m+1;rc=walk(r);lo[i]=a
        return 1+lc+rc
    return walk(x)

def main():
    bundle={}
    for letter in ('a','b'):
        part=json.loads(Path(__file__).with_name('seven-overlap-certificates-'+letter+'.json').read_text())
        assert not (part.keys() & bundle.keys())
        bundle.update(part)
    chosen=sys.argv[1:] or sorted(bundle)
    assert set(bundle)=={str(h)+str(c) for h in (1,2) for c in range(4)}
    for name in chosen:
        h,c=map(int,name);ct,seen=cstats(h,c);ks=sorted(seen)
        rec=bundle[name];records=[]
        assert ct==rec['raw'] and len(ks)==rec['unique']
        sha=hashlib.sha256(b''.join(n.to_bytes(4,'little') for z in ks for n in z)).hexdigest()
        assert sha==rec['sha256']
        for part in rec['parts']:records.extend(json.loads(zlib.decompress(base64.b85decode(part)).decode()))
        assert len(records)==len(ks)
        counts=Counter();nodes=0
        for z,r in zip(ks,records):
            counts[r[0]]+=1;nodes+=verifyone(z,r)
        assert dict(counts)==rec['method_counts'] and nodes==rec['tree_nodes']
        print(name,'raw',ct,'unique',len(ks),dict(counts),'tree nodes',nodes,sha)
if __name__=='__main__':main()
