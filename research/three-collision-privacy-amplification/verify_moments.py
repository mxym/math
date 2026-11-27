#!/usr/bin/env python3
"""Exact finite collision and central-moment checks, using explicit hash tables."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb

def bit(x):
    return x.bit_count() & 1

def affine_tables(d,m):
    for rows in product(range(1<<(d+1)),repeat=m):
        yield tuple(sum(bit(r & (x|(1<<d))) << j for j,r in enumerate(rows))
                    for x in range(1<<d))

def verify_joint(tables,M,k):
    n=len(tables[0])
    for i in range(1,min(k,n)+1):
        for inds in combinations(range(n),i):
            vals=Counter(tuple(t[x] for x in inds) for t in tables)
            assert len(vals)==M**i
            assert set(vals.values())=={len(tables)//M**i}

def moments(tables,M,weights):
    p=Q(1,M)
    counts=Counter()
    for table in tables:
        bins=[Q(0)]*M
        for z,w in zip(table,weights):
            bins[z]+=w
        counts.update(z-p for z in bins)
    assert sum(counts.values())==len(tables)*M
    exp=lambda h: sum(n*h(z) for z,n in counts.items())/(len(tables)*M)
    assert exp(lambda z:z)==0
    a=exp(lambda z:max(z,0))
    v=exp(lambda z:z*z)
    w=exp(lambda z:z*z*z)
    c2=sum(x*x for x in weights)
    c3=sum(x*x*x for x in weights)
    assert v==p*(1-p)*c2
    assert w==p*(1-p)*(1-2*p)*c3
    lower=(1-p)*c2*c2/(2*p*c2+(1-2*p)*c3)
    assert M*a>=lower>0
    if len(set(x for x in weights if x))==1:
        n=sum(x>0 for x in weights)
        assert lower==Q(M-1,2*n+M-2)
    return M*a

rand_tables=0
for n in range(1,5):
    for M in range(2,5):
        tabs=list(product(range(M),repeat=n))
        verify_joint(tabs,M,3)
        for raw in ([1]*n,list(range(1,n+1)),[0]*(n-1)+[1]):
            w=[Q(a,sum(raw)) for a in raw]
            moments(tabs,M,w)
            rand_tables+=1
print(f"independent raw tables (including odd bin counts), exact weighted moments: {rand_tables} PASS")

cases=0
for d,m in ((1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)):
    M=1<<m
    tabs=list(affine_tables(d,m))
    verify_joint(tabs,M,3)
    if d>=2:
        assert Q(sum(len(set(t[:4]))==1 for t in tabs),len(tabs))==Q(1,M*M)
        assert Q(1,M*M)>Q(1,M**3)
    N=1<<d
    for raw in ([1]*N,list(range(1,N+1)),[i%3 for i in range(N)]):
        w=[Q(a,sum(raw)) for a in raw]
        moments(tabs,M,w)
        cases+=1
print(f"strong-three binary affine tables, fourth-collision negative control: {cases} PASS")

# Exact two-wise, not three-star: project multiplication in F_4 to its whole F_4.
def fm(a,b):
    v=0
    for _ in range(2):
        if b&1:v^=a
        b>>=1
        a<<=1
        if a&4:a^=7
    return v
tabs=[tuple(fm(a,x)^b for x in range(4)) for a,b in product(range(4),repeat=2)]
verify_joint(tabs,4,2)
assert Q(sum(len(set(t[:3]))==1 for t in tabs),len(tabs))==Q(1,4)>Q(1,16)
error=sum(sum(abs(Q(t.count(z),4)-Q(1,4))/2 for z in range(4))
          for t in tabs)/len(tabs)
assert error==Q(3,16) < Q(4-1,2*4+4-2)
print("exact-two-only field-affine family: third-moment negative control PASS")

# Binary-output exchangeable optimum, directly checking all specified
# positive/negative sign patterns of at most three fixed coordinates.
def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0
for N in range(1,25):
    if N==1:
        choose_sum={1:Q(1,2),-1:Q(1,2)}
    else:
        a=N%2
        heavy=Q(N-a*a,N*N-a*a)
        choose_sum={N:heavy/2,-N:heavy/2}
        if a:
            choose_sum[a]=choose_sum[-a]=(1-heavy)/2
        else:
            choose_sum[0]=1-heavy
    assert sum(choose_sum.values())==1
    assert sum(v*s*s for s,v in choose_sum.items())==N
    for k in range(1,min(3,N)+1):
        for j in range(k+1):
            prob=sum(v*Q(choose(N-k,(N+s)//2-j),choose(N,(N+s)//2))
                     for s,v in choose_sum.items())
            assert prob==Q(1,1<<k)
    tv=sum(Q(abs(s),2*N)*v for s,v in choose_sum.items())
    assert tv==(Q(1,N+1) if N%2 else Q(1,2*N))
print("binary-output exact optimum: 24 support sizes PASS")

# The inequality-only definition has a zero-error negative control
# even at fourth order: uniform balanced maps with N divisible by M.
tb=[t for t in product(range(3),repeat=6) if all(t.count(z)==2 for z in range(3))]
assert tb
for k in range(2,7):
    for sub in combinations(range(6),k):
        v=Q(sum(len({t[i] for i in sub})==1 for t in tb),len(tb))
        assert v<=Q(1,3**(k-1))
assert all(tuple(t.count(z) for z in range(3))==(2,2,2) for t in tb)
print("balanced zero-error family with inequality-only collisions: PASS")
