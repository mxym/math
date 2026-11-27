#!/usr/bin/env python3
"""Exact cyclotomic construction and rational scalar checks."""
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache

def trim(x):
    while len(x)>1 and x[-1]==0:
        x.pop()
    return x

def divrem(a,b):
    a=trim(list(a))
    q=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        k=len(a)-len(b)
        t=a[-1]
        q[k]=t
        for j,c in enumerate(b):
            a[k+j]-=t*c
        trim(a)
    return trim(q),a

@lru_cache(None)
def cyclo(n):
    a=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:
            a,r=divrem(a,cyclo(d))
            assert r==[0]
    return a

class Ring:
    def __init__(self,n):
        self.n=n
        self.f=cyclo(n)
        self.one=(1,)
        self.zero=(0,)
    def elem(self,a):
        return tuple(divrem(a,self.f)[1])
    def add(self,*ps):
        out=[0]*max(map(len,ps),default=1)
        for p in ps:
            for i,v in enumerate(p):
                out[i]+=v
        return self.elem(out)
    def mul(self,a,b):
        out=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                out[i+j]+=x*y
        return self.elem(out)
    def scale(self,a,p):
        return self.elem([a*x for x in p])
    def pow(self,k):
        return self.elem([0]*(k%self.n)+[1])
    def conj(self,a):
        return self.add(*(self.scale(x,self.pow(-i)) for i,x in enumerate(a)))

fourier=0
for n in range(2,13):
    R=Ring(n)
    for k in range(n):
        assert R.add(*(R.pow(j*k) for j in range(n)))==((n,) if k==0 else R.zero)
    for d in range(1,n):
        # Compute nP exactly in Q[zeta_n], where P is the first-d Fourier projection.
        S=[[R.add(*(R.pow((i-j)*k) for k in range(d)))
            for j in range(n)] for i in range(n)]
        for i,j in product(range(n),repeat=2):
            v=R.add(*(R.mul(S[i][k],S[k][j]) for k in range(n)))
            assert v==R.scale(n,S[i][j])
            assert S[i][j]==R.conj(S[j][i])
            fourier+=2
        assert all(S[x][x]==(d,) for x in range(n))
        a=Q(d,n)
        for i in range(n):
            Pr=[R.scale(Q(1,n),S[j][i]) for j in range(n)]
            Ur=[R.add((int(j==i),),R.scale(-1,Pr[j])) for j in range(n)]
            assert Pr[i]==(a,) and Ur[i]==(1-a,)
            for u,v in [(Q(1),Q(0)),(Q(5),Q(2)),(Q(7),Q(6)),(Q(1),Q(1))]:
                # Sign choice in the positive real scalings ensures (population >= a).
                den=u*u*a+v*v*(1-a)
                b=u*u*a/den
                s=(u*a+v*(1-a))**2/den
                assert u>=v and a<=b<=1
                assert 0<=s<=1
                # Compare to expanded squared binary fidelity without approximating radicals.
                lin=a*b+(1-a)*(1-b)
                assert s>=lin and (s-lin)**2==4*a*(1-a)*b*(1-b)
                fourier+=3
print(f"exact cyclotomic projection and attainment checks: {fourier}")

sq={}
for u,v in [(0,1),(1,1),(3,5),(4,5),(5,13),(12,13),(8,17),(15,17),
            (7,25),(24,25),(20,29),(21,29)]:
    a=Q(u,v)**2
    q=(1-a)
    # Known Pythagorean complements.
    from math import isqrt
    assert isqrt(q.numerator)**2==q.numerator and isqrt(q.denominator)**2==q.denominator
    sq[a]=(Q(u,v),Q(isqrt(q.numerator),isqrt(q.denominator)))

def val(a,b,capped):
    if capped and a>=b:
        return Q(1)
    v,w=sq[a]
    z,t=sq[b]
    return (v*z+w*t)**2

def ge(a,b,target,capped):
    if capped and a>=b:
        return target<=1
    lin=a*b+(1-a)*(1-b)
    return lin>=target or (target-lin)**2<=4*a*(1-a)*b*(1-b)

co=0
ab=list(product(sq,sq))
for (a,b),(x,y),l,cap in product(ab,ab,[Q(1,3),Q(1,2),Q(3,5)],range(2)):
    rhs=l*val(a,b,cap)+(1-l)*val(x,y,cap)
    assert ge(l*a+(1-l)*x,l*b+(1-l)*y,rhs,cap)
    co+=1
print(f"exact two-variable Jensen checks: {co}")

# Nonuniform unequal budgets: normalizing the inverse interior derivatives
# engineers two active labels with a common weighted marginal gain. The
# third label wants full subspace population but has smaller prior weight.
a=[Q(9,25),Q(16,25),Q(0)]
b=[Q(16,25),Q(144,169),Q(1)]
def derivative(a,b):
    u,v=sq[a]
    w,z=sq[b]
    return 2*b-1+(1-2*a)*w*z/(u*v)
raw=[1/derivative(a[i],b[i]) for i in range(2)]+[Q(1,2)]
mu=1/sum(raw)
p=[mu*x for x in raw]
assert sum(p)==1 and sum(a)==1 and p[2]<mu
assert all(p[i]*derivative(a[i],b[i])==mu for i in range(2))
out=sum(w*val(x,y,True) for x,y,w in zip(a,b,p))
assert 0<out<1
print("exact heterogeneous derivative/tie witness: pass")

# Hard saturation and d=0 are essential. Distinct labels can yield
# success 1 already at eps=1-d/n, and not the un-clipped decreasing branch.
assert val(Q(9,25),Q(0,1),False)==Q(16,25)
assert val(Q(9,25),Q(0,1),True)==1
assert ge(Q(4,5)**2,Q(0),Q(1),True)
print("negative control: unclipped extension beyond threshold gives the wrong optimum")
