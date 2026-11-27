#!/usr/bin/env python3
"""Finite orbit test for point-transitive kissing in dimension six. Standard library only.
No floating point operation affects acceptance. Run without python -O.
"""
sys_dont_optimize = __debug__
if not sys_dont_optimize: raise RuntimeError("run with assertions enabled")
from fractions import Fraction as F
from functools import lru_cache
import math

Q=10**24
# pi/4 = atan(1/2)+atan(1/3), by the addition law and the first quadrant.
def atan_box(q):
    s=sum((F((-1)**i,(2*i+1)*q**(2*i+1)) for i in range(60)),F())
    return s,s+F(1,121*q**121)
p=F(314159265358979323846264338327,10**29)
L,H=atan_box(2); l,h=atan_box(3)
assert p<4*(L+l)<4*(H+h)<p+F(1,10**29)
@lru_cache(None)
def table(m):
    assert 3<=m<=10**8
    # Rounded complex rotation; component error at most 2/Q after floor.
    z=2*p/m; T=F(1); C=F(1); S=F(0)
    for j in range(1,43):
        T*=z/j
        if j%4==0:C+=T
        if j%4==1:S+=T
        if j%4==2:C-=T
        if j%4==3:S-=T
    assert z**43/math.factorial(43)+2*F(1,10**29)/m<F(1,Q)
    a,b=(v.numerator//v.denominator for v in (Q*C,Q*S))
    x,y=Q,0; boxes=[(Q,Q)]
    for j in range(1,m//2+1):
        x,y=(a*x-b*y)//Q,(a*y+b*x)//Q
        # True rotation preserves norm. Approximate rotation differs in
        # operator 2-norm by <3/Q; rounded vector has norm <=2 by induction;
        # floor costs <2/Q. Therefore error increases by <8/Q per step.
        boxes.append((max(-Q,x-8*j),min(Q,x+8*j)))
    return boxes
def at(m,j):
    j%=m; return table(m)[min(j,m-j)]

from fractions import Fraction as F
from itertools import combinations,product,combinations_with_replacement
import math
from functools import lru_cache

D=1000000
def clip(P,a,b):
    if not P:return []
    R=[]
    for x,y in zip(P,P[1:]+P[:1]):
        tx=sum(u*v for u,v in zip(a,x))-b;ty=sum(u*v for u,v in zip(a,y))-b
        if tx<=0:R.append(x)
        if tx*ty<0:R.append(tuple((ty*i-tx*j)/(ty-tx) for i,j in zip(x,y)))
    return list(dict.fromkeys(R))
unit=[(F(1),F(0),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1))]
def orbitpoly(m,act):
    P=unit[:]
    for g in act[1:]:
        a=[at(m,k)[0]*D//Q for k in g]
        P=clip(P,a,F(D,2))
        if not P:break
    return P
def frequency_sets(m,r):
    # Every faithful prime-power cyclic action has a unit frequency. Rescale it to 1.
    def canon(K):
        def ab(x):return min(x%m,(-x)%m)
        return min(tuple(sorted(ab(pow(k,-1,m)*t) for t in K)) for k in K if math.gcd(k,m)==1)
    return sorted({canon((1,)+ks) for ks in combinations(range(2,m//2+1),r-1)})
def types(m):
    for K in frequency_sets(m,3):
        A=[tuple(j*k%m for k in K) for j in range(m)]
        yield 'C',K,m,A,(m,1,1)
    if m==25:
        for H in [(0,1,1),(0,1,2),(1,1,1),(1,1,2)]:
            A=[v for v in product(range(5),repeat=3) if sum(i*j for i,j in zip(H,v))%5==0]
            yield 'F',H,5,A,(5,5,1)
def radiuscells(P,level):
    if level==0:return [P]
    j=max(range(3),key=lambda i:max(v[i] for v in P)-min(v[i] for v in P))
    t=(max(v[j] for v in P)+min(v[j] for v in P))/2
    v=[0]*3;v[j]=1
    return radiuscells(clip(P,v,t),level-1)+radiuscells(clip(P,[-z for z in v],-t),level-1)
def coeffs(P,R):
    K=[];L=[]
    for x,y in product(P,R):
        lo=[];hi=[]
        for a,b in zip(x,y):
            f=a*b*D*D;l=math.isqrt(f.numerator//f.denominator);lo.append(l)
            h=(a+b)*D/2;hi.append(-(-h.numerator//h.denominator))
        K.append(lo);L.append(hi)
    return list(zip(K,L))
class Phase:
    def __init__(self,m,A,ds,grid=64):
        self.ds=ds;self.N=N=m*grid;self.st=[tuple(t*grid for t in g) for g in A]
        self.cs=[at(N,i)[0]*D//Q for i in range(N)]
    @lru_cache(None)
    def column(self,j,x,h):
        N=self.N
        return tuple(-D if (N//2-(g[j]+x))%N<=h else min(self.cs[(g[j]+x)%N],self.cs[(g[j]+x+h)%N]) for g in self.st)
    def certify(self,P,R):
        pars=coeffs(P,R);N=self.N;ini=tuple((0,N//t) for t in self.ds)
        nodes=0
        def rec(box):
            nonlocal nodes
            nodes+=1
            for C in zip(*(self.column(i,x,h) for i,(x,h) in enumerate(box))):
                a,b,c=C
                if all(a*(lo if a>=0 else hi)[0]+b*(lo if b>=0 else hi)[1]+c*(lo if c>=0 else hi)[2]>D**2//2 for lo,hi in pars):return True
            j=max(range(3),key=lambda i:box[i][1]);x,h=box[j]
            if h<=1:return False # inconclusive, never a proof that the orbits exist
            h1=h//2
            for z in [(x,h1),(x+h1,h-h1)]:
                b=list(box);b[j]=z
                if not rec(b):return False
            return True
        return rec(ini),nodes
def orbit_test():
    result={}; total=0
    for order in (37,25):
        counts={}
        for lab,K,m,A,ds in types(order):
            P=orbitpoly(m,A)
            if not P:continue
            counts[lab]=counts.get(lab,0)+1
            alg=Phase(m,A,ds);bad=None
            for lev in range(5):
                cs=radiuscells(P,lev);new=set()
                for i,j in combinations_with_replacement(range(len(cs)),2):
                    if bad is not None and (i//2,j//2) not in bad:continue
                    ok,z=alg.certify(cs[i],cs[j]);total+=z
                    if not ok:new.add((i,j))
                bad=new
                tri=any((i,j) in bad and (j,k) in bad and (i,k) in bad for i,j,k in combinations_with_replacement(range(len(cs)),3))
                if not bad or (order==25 and not tri):break
            else:raise RuntimeError(('unresolved',order,K,bad))
            alg.column.cache_clear()
        result[order]=counts
    assert result=={37:{'C':6},25:{'C':13,'F':1}}
    print('No two 37-orbits; no three 25-orbits.',result,'phase boxes:',total)
def prime_table():
    primes=[p for p in range(7,133) if all(p%q for q in range(2,math.isqrt(p)+1))]
    U={}
    for p in primes:
        r=1 if p<=13 else 2 if p<=41 else 3
        for K in frequency_sets(p,r):
            # pad to three columns; this does not change feasibility.
            J=K+(K[-1],)*(3-r)
            A=[tuple(i*k%p for k in J) for i in range(p)]
            assert not orbitpoly(p,A),(p,K)
        U[p]=r+1
    for n,Ns in [(6,range(73,77)),(7,range(127,133))]:
        for N in Ns:
            possible={2,3,5}
            for p,r in U.items():
                s=n-2*r
                if s<0 or p>N:continue
                fixed=[0,2,6,12][s]
                if N%p<=fixed:possible.add(p)
            if n==6 and N==74:possible.discard(37) # ruled out by orbit_test
            expected={2,3,5,7} if n==6 else {2,3,5,7,11,13}
            if (n,N)==(6,76):expected.add(19)
            assert possible==expected,(n,N,possible)
    print('Prime-order rotation and fixed-subspace census passed through 132.')
if __name__=='__main__':
    prime_table();orbit_test()
