#!/usr/bin/env python3
"""Exact rational auxiliary checks for OneWayRelativeEntropy.md.

The proof is analytic. The tests use only standard-library rational
arithmetic, including outward bounds on logarithms and exponentials.
"""
from fractions import Fraction as Q
from random import Random

def clipped(p,q,k):
    # Guess the set with k*p_i/q_i at most the water level, and solve
    # the one remaining linear normalization equation.
    ratios=[k*x/y for x,y in zip(p,q)]
    for b in (Q(0),*sorted(set(ratios)),Q(1)):
        inactive=[i for i,x in enumerate(ratios) if x<=b]
        if not inactive:continue
        w=(1-sum(k*p[i] for i in range(len(p)) if i not in inactive))/sum(q[i] for i in inactive)
        if w<b:continue
        if all(ratios[i]<=w for i in inactive) and all(ratios[i]>=w for i in range(len(p)) if i not in inactive):
            r=tuple(max(k*x,w*y) for x,y in zip(p,q))
            assert 0<=w<=1 and sum(r)==1
            return r,w
    raise AssertionError("no water level")

def stick(p,q,t):return sum(max(Q(0),x-t*y) for x,y in zip(p,q))
def clip_checks(p,q,k):
    r,b=clipped(p,q,k)
    breaks=sorted({Q(0),Q(1),b,*(k*x/y for x,y in zip(p,q)),*(x/y for x,y in zip(r,q))})
    for t in breaks+[(x+y)/2 for x,y in zip(breaks,breaks[1:])]+[breaks[-1]+1]:
        assert stick(r,q,t)==max(1-t,Q(0),k*stick(p,q,t/k))
    flag=tuple(k*x/y for x,y in zip(p,r))
    assert all(0<=x<=1 for x in flag)
    assert sum(x*y for x,y in zip(r,flag))==k
    assert sum(x*(1-y) for x,y in zip(r,flag))==1-k
    assert all(x*y==k*z for x,y,z in zip(r,flag,p))
    return r

B=2**84
def down(x):return Q(x*B//1,B)
def up(x):return -down(-x)
def roundbox(lo,hi):return down(lo),up(hi)

def series(y):
    z=(y-1)/(y+1);assert 0<=z<=Q(1,3)
    v=z;s=Q(0);n=32
    for i in range(n):
        s+=v/(2*i+1);v*=z*z
    return (2*s,2*s+2*v/((2*n+1)*(1-z*z)))
L2=series(Q(2))
def logbox(x):
    assert x>0
    m=0
    while x>2:m+=1;x/=2
    while x<1:m-=1;x*=2
    l,u=series(x)
    return roundbox(l+m*L2[int(m<0)],u+m*L2[int(m>=0)])

def dbox(p,q):
    lo=hi=Q(0)
    for x,y in zip(p,q):
        if not x:continue
        a,b=logbox(x/y);lo+=x*a;hi+=x*b
    return roundbox(lo,hi)

def expneg(x):
    assert x>=0
    m=0
    while x>Q(1,2):x/=2;m+=1
    s=t=Q(1)
    for n in range(1,34):
        t*=(-x)/n;s+=t
    l,u=roundbox(s,s-t) # 33 terms after the constant: odd partial sum.
    for _ in range(m):l,u=roundbox(l*l,u*u)
    return l,u

def binary_upper(k,rlo,rhi):
    d=1-k
    return k*(logbox(k)[1]-logbox(rlo)[0])+d*(logbox(d)[1]-logbox(1-rhi)[0])

rng=Random(20261127)
certified=0
for _ in range(240):
    n=rng.randrange(3,7)
    p0=[rng.randrange(15) for _ in range(n)]
    if not sum(p0):p0[0]=1
    q0=[rng.randrange(1,20) for _ in range(n)]
    p=tuple(Q(x,sum(p0)) for x in p0);q=tuple(Q(x,sum(q0)) for x in q0)
    k=rng.choice([Q(7,8),Q(13,16),Q(3,4),Q(5,8),Q(1,2),Q(1,4)])
    r=clip_checks(p,q,k)
    a,b=dbox(p,q)
    if a<=0 or len({x/y for x,y in zip(p,q) if x})==1:continue
    rlo=expneg(b)[0];rhi=expneg(a)[1]
    if k<=rlo:
        assert dbox(r,q)[0]>=0
    elif k>rhi:
        assert dbox(r,q)[0]>binary_upper(k,rlo,rhi)
    else:continue
    certified+=1
assert certified>=225

# Sharp two-point families, including the exact boundary.
for n in range(2,15):
    q=(Q(1,n),Q(n-1,n));p=(Q(1),Q(0))
    for k in [Q(1,2*n),Q(1,n),Q(n+1,2*n),Q(n-1,n)]:
        r=clip_checks(p,q,k)
        assert r==((k,1-k) if k>=q[0] else q)
        assert r[0]>=k
# For CQ scalar certificate the comparisons are exactly rational after
# exponentiating the entropy secants and squaring the plateau endpoints.
assert Q(84375,65536)<Q(3,2)
assert Q(27,16)<Q(8,3)
assert 16>4*3
assert all(4*(d*d-1)>d*d for d in range(3,100))
# Isotropic sharpness, each marginal unchanged, exact spectral masses.
for d in range(2,8):
    N=d*d
    phi={(i*d+i,j*d+j):Q(1,d) for i in range(d) for j in range(d)}
    for i in range(N):
        for j in range(N):
            assert sum(phi.get((i,k),0)*phi.get((k,j),0) for k in range(N))==phi.get((i,j),0)
    t=Q(N-1,2*N)
    # Eigenvalues on the range of phi and on its orthogonal complement:
    a,b=1-t,t/(N-1)
    R=lambda i,j: (a-b)*phi.get((i,j),0)+b*(i==j)
    for i in range(d):
        for j in range(d):
            assert sum(R(i*d+k,j*d+k) for k in range(d))==Q(i==j,d)
            assert sum(R(k*d+i,k*d+j) for k in range(d))==Q(i==j,d)
    assert a+b*(N-1)==1 and (abs(a-1)+(N-1)*b)/2==t
print(f"PASS: 292 rational clipping/flag examples, {certified} rigorous entropy comparisons, 6 exact quantum sharpness families.")
