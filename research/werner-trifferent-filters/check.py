"""Exact finite checks for the analytic argument (standard library, no inputs)."""
from fractions import Fraction as F
from itertools import product, combinations
from collections import defaultdict, Counter

def verify(flag,name):
    if not flag: raise ArithmeticError(name)
def distance(a,b):
    return sum(i!=j for i,j in zip(a,b))
def tcode(k):
    vs=list(product(range(3),repeat=k))
    ls=[v for v in vs if next((z for z in v if z),0)==1]
    return [tuple(sum(i*j for i,j in zip(a,l))%3 for l in ls) for a in vs]
def triff(A):
    return all(any(len(set(c))==3 for c in zip(*v)) for v in combinations(A,3))
def key(x,y):
    return tuple((i,a,b) for i,(a,b) in enumerate(zip(x,y)) if a!=b)
def rpresent(mat,idx):
    return mat.get(idx,0)
def add(mat,i,j,v):
    if v:
        key0=(min(i,j),max(i,j))
        mat[key0]=mat.get(key0,0)+v
        if mat[key0]==0:del mat[key0]

A=tcode(2);d=3;n=len(A[0]);D=3;W=list(product(range(d),repeat=n))
omega=[(x,y) for x in A for y in W]
idx={v:i for i,v in enumerate(omega)}
sector=defaultdict(list)
for xy in omega:sector[key(*xy)].append(xy)
checkcode=tcode(3)
verify(triff(A) and triff(checkcode),'trifference')
verify(all(distance(a,b)==9 for a,b in combinations(checkcode,2)),'k3 distance')
verify(all(distance(a,b)==D for a,b in combinations(A,2)),'k2 distance')

def rawmatrix(p,q):
    # Actual product of n one-site factors, scaled by q^n.
    M={}
    for i,(a,b) in enumerate(omega):
        for j in range(i,len(omega)):
            c,e=omega[j];v=1
            for x,y,u,w in zip(a,b,c,e):
                v*=(q if x==u and y==w else 0)-(p if x==y and u==w else 0)
                if not v:break
            if v: M[i,j]=v
    return M
def sector_werner(p,q):
    # Independent reconstruction of ALL coefficients using the local embeddings.
    t=F(p,q); z=t/(1-t);L=z**D; tau=L/(1+L); remaining={}; embedded={}
    for K,V in sector.items():
        pref=(1-t)**(n-len(K))*q**n
        if len(V)==1:
            ii=idx[V[0]];remaining[ii]=pref;continue
        I=[a for a,b in V]; J=[b for a,b in V]
        # Embed (1+L)*(I-tau |Omega><Omega|), scaled by pref.
        for a in I:
            for b in J:
                ii=idx[a,b];add(embedded,ii,ii,pref*(1+L))
        ids=[idx[v] for v in V]
        for k,i in enumerate(ids):
            for j in ids[k:]:
                add(embedded,i,j,-pref*(1+L)*tau)
    used=set()
    for K,V in sector.items():
        if len(V)==1:continue
        pref=(1-t)**(n-len(K))*q**n
        for a,b in V:
            for c,e in V:
                if a==c:continue
                i=idx[a,e]
                verify(i in remaining and i not in used,'singleton disjointness')
                verify(remaining[i]==pref*(1-t)**(-D),'charge weight')
                used.add(i);remaining[i]-=pref*(1+L)
    verify(all(v>=0 for v in remaining.values()),'positive diagonal residual')
    for i,val in remaining.items():add(embedded,i,i,val)
    return embedded
for p,q in [(0,1),(1,3),(1,2),(3,5)]:
    raw=rawmatrix(p,q);M=sector_werner(p,q)
    verify(M==raw,'full operator identity')
    for r in range(2,10):
        sel=[idx[a,a] for a in A[:r]]
        val=sum(raw.get((min(i,j),max(i,j)),0) for i in sel for j in sel)
        verify(val==r*(q-p)**(n-D)*((q-p)**D-(r-1)*p**D),'sharp diagonal test')
    print('tetra t=%d/%d: full operator identity; all eight test ranks checked'%(p,q))

# t=1 endpoint: use mismatch on the agreement sites.
raw=rawmatrix(1,1);a,b=A[:2]
X=tuple((x+1)%3 if x==y else x for x,y in zip(a,b))
Y=tuple((y+1)%3 if x==y else y for x,y in zip(a,b))
i,j=idx[a,X],idx[b,Y]
verify(raw.get((i,i),0)==raw.get((j,j),0)==0 and raw.get((min(i,j),max(i,j)),0)==-1,'t=1')
print('t=1: negative two-word witness verified')
# Classify dimension-two ternary supports directly.
def safe(B):
    return all(sum(len(set(c))==3 for c in zip(*tr))%2==0 for tr in combinations(B,3))
ws=list(product(range(3),repeat=2));mx=fm=0
for mask in range(1,1<<len(ws)):
    B=[ws[i] for i in range(len(ws)) if mask&(1<<i)]
    if safe(B):
        mx=max(mx,len(B))
        if all(len({a[j] for a in B})==3 for j in range(2)):fm=max(fm,len(B))
verify((mx,fm)==(4,3),'sharp dimensions')
for n_ in range(2,8):
    B=[u for u in product(range(2),repeat=n_) if sum(u)%2==0]+[(2,)*n_]
    verify(safe(B) and len(B)==2**(n_-1)+1,'all-rank construction')
print('coordinate-support sanity checks passed')
