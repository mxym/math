#!/usr/bin/env python3
"""Exact PSL2(7) multi-orbit certificate, with no nonstandard dependencies.
Use --vertices for a second implementation of the interval exclusions."""
from itertools import product,combinations
from functools import lru_cache
from fractions import Fraction as F
from math import comb,factorial,prod
import sys
if not __debug__:raise RuntimeError("assertions required")
VERT="--vertices" in sys.argv
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def mat(A,B):return tuple(tuple(dot(row,col) for col in zip(*B)) for row in A)
def tx(A):return tuple(zip(*A))
I=tuple(range(8))
group=set()
for a,b,c,d in product(range(7),repeat=4):
    if (a*d-b*c)%7!=1:continue
    def apply(x):
        h,k=((a*x+b)%7,(c*x+d)%7) if x<7 else (a,c)
        return h*pow(k,-1,7)%7 if k else 7
    group.add(tuple(map(apply,I)))
assert len(group)==168
G=sorted(group)
def mul(p,q):return tuple(p[k] for k in q)
def cyclic(g):
    a={I};h=g
    while h not in a:a.add(h);h=mul(h,g)
    return a
def parts(H):
    S=set(I);res=[]
    while S:
        s={g[min(S)]for g in H};res.append(tuple(sorted(s)));S-=s
    return sorted(res,key=lambda t:(len(t),t))
B4=[]
remaining=set(combinations(I,4))
while remaining:
    seed=min(remaining);s={tuple(sorted(g[i]for i in seed))for g in G};remaining-=s;B4.append(sorted(s))
assert list(map(len,B4))==[42,14,14]
assert all(tuple(sorted(set(I)-set(s))) in orbit for orbit in B4 for s in orbit)
outer=tuple((3*i)%7 if i<7 else 7 for i in I)
assert [next(j for j,L in enumerate(B4) if tuple(sorted(outer[i]for i in o[0])) in L)for o in B4]==[0,2,1]
def flat(M):return tuple(t for row in M for t in row)
def quad(C,z,w):
    a,b,c,d,e,f,g,h,i=C;x,y,t=z;X,Y,T=w
    return x*(a*X+b*Y+c*T)+y*(d*X+e*Y+f*T)+t*(g*X+h*Y+i*T)
@lru_cache(None)
def data(k,bits,simp):
    g=next(g for g in G if len(cyclic(g))==k);H=cyclic(g);bs=parts(H);m=list(map(len,bs))
    assert m==([2,2,2,2]if k==2 else [1,1,3,3])
    W=tuple(tuple((m[3] if i in bs[j] else 0)-(m[j] if i in bs[3] else 0)for j in range(3))for i in I)
    S=flat(mat(tx(W),W))
    D=[flat(mat(tx(W),[W[i]for i in g])) for g in G]
    C={tuple(M[3*i+j]+M[3*j+i]-S[3*i+j]for i in range(3)for j in range(3))for M,h in zip(D,G)if h not in H}
    if simp:
        for w in W:C.add(tuple(32*w[i]*w[j]-7*S[3*i+j]for i in range(3)for j in range(3)))
    for e,orb in enumerate(B4):
        if bits>>e&1:
            for o in orb:
                w=[sum((1 if t in o else -1)*W[t][j]for t in I)for j in range(3)]
                C.add(tuple(w[i]*w[j]-2*S[3*i+j]for i in range(3)for j in range(3)))
    return W,S,sorted(C),sorted(set(D)),bs
def axes(f):return tuple(i for i in range(3) if i!=abs(f)-1)
@lru_cache(None)
def verts(f,z):
    u,v=axes(f)
    return tuple(tuple(x+int(i==u)*a+int(i==v)*b for i,x in enumerate(z))for a,b in product((-1,1),repeat=2))
def kids(f,z):return verts(f,tuple(2*x for x in z))
def rootcone(W,bs,vs):
    for s in [-1,1]:
        passes=True
        for z in vs:
            a,b,c,d=[dot(W[o[0]],z)for o in bs]
            if not (s*(a-b)>4*abs(c+d) and 2*s*(a-b)>abs(c-d)):passes=False;break
        if passes:return True
    return False
def lower(A,z,f,w,h):
    u,v=axes(f);i,j=axes(h)
    if VERT:return min(quad(A,x,y)for x in verts(f,z)for y in verts(h,w))
    R=lambda r:dot(A[3*r:3*r+3],w)
    C=lambda c:dot(A[c::3],z)
    return quad(A,z,w)-abs(R(u))-abs(R(v))-abs(C(i))-abs(C(j))-sum(abs(A[3*l+m])for l in (u,v)for m in (i,j))
@lru_cache(None)
def ok(k,bits,simp,f,z):
    W,S,C,D,bs=data(k,bits,simp)
    if (k,bits,simp)==(3,7,False) and rootcone(W,bs,verts(f,z)):return False
    return not any(lower(A,z,f,z,f)>0 for A in C)
def boxes(k,bits,simp,L):
    out=[];nodes=0
    for f in (-3,-2,-1,1,2,3):
        stack=[(tuple((1 if f>0 else -1) if i==abs(f)-1 else 0 for i in range(3)),0)]
        while stack:
            z,d=stack.pop();nodes+=1
            if not ok(k,bits,simp,f,z):continue
            if d==L:out.append((f,z));continue
            stack.extend((t,d+1)for t in kids(f,z))
    return out,nodes
def pair_test():
    W,S,C,D,bs=data(3,0,True);bs,nodes=boxes(3,0,True,3);n=0
    @lru_cache(None)
    def norm(f,z):return max(quad(S,x,x)for x in verts(f,z))
    def dfs(f,z,h,w,a,b):
        nonlocal n
        n+=1
        if not ok(3,0,True,f,z) or not ok(3,0,True,h,w):return
        Q=norm(f,z)*norm(h,w)
        for T in D:
            l=lower(T,z,f,w,h)
            if l>0 and 4*l*l>Q:return
        assert max(a,b)<14,("open pair",f,z,h,w)
        if a<=b:
            for x in kids(f,z):dfs(f,x,h,w,a+1,b)
        else:
            for y in kids(h,w):dfs(f,z,h,y,a,b+1)
    for f,z in bs:
        if f<0:continue # simultaneous negation of both representatives
        for h,w in bs:dfs(f,z,h,w,3,3)
    return n
def partitions(n,m=None):
    if not n:yield ();return
    for i in range(min(n,m or n),0,-1):
        for t in partitions(n-i,i):yield (i,)+t
def hooks(mu):
    return factorial(sum(mu))//prod(mu[i]-j+sum(j<r for r in mu[i+1:]) for i in range(len(mu))for j in range(mu[i]))
def transpose(mu):return tuple(sum(t>=k for t in mu)for k in range(1,mu[0]+1))
def finite_checks():
    P=list(partitions(8))
    assert {p for p in P if hooks(p)==7}=={(7,1),(2,1,1,1,1,1,1)}
    assert not [p for p in P if p==transpose(p) and hooks(p)==14]
    counts={m:sorted(p for p in P if factorial(8)//prod(map(factorial,p))==m)for m in range(2,133)}
    assert {m:ps for m,ps in counts.items()if ps}=={8:[(7,1)],28:[(6,2)],56:[(5,3),(6,1,1)],70:[(4,4)]}
    for N in range(126,133):
        out=[(a,b,c,d)for a,b,c,d in product(range(3),range(3),range(3),range(2))if 8*a+28*b+56*c+70*d==N]
        assert set(out)==({(0,0,1,1),(0,2,0,1)} if N==126 else {(2,0,2,0),(2,2,1,0)} if N==128 else set())
        out=[a for a in range(3)if (N-8*a)%14==0]
        assert out==([0]if N==126 else [2]if N==128 else [])
    for k in range(3,7):assert 2**k*comb(7,k)>132
    assert 49+63+28*14==504 and F(14+49,9)==7
if __name__=="__main__":
    finite_checks()
    tests=[(2,0,True),(3,1,True),(3,2,True),(3,4,True),(2,1,False),(3,7,False)]
    print("Mode:","vertex enclosure" if VERT else "center enclosure")
    for k,b,s in tests:
        survivors,n=boxes(k,b,s,7)
        assert not survivors,(k,b,s,survivors[:2])
        print("single",k,b,s,n,flush=True)
    print("pair",pair_test(),flush=True)
