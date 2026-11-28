"""Fixed numerical distinction between edge rank, canonical aggregates and other trees."""
from itertools import combinations
from math import isqrt,prod
from fractions import Fraction as F

def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def graph(vs,S,E):
    return {(p,q):[m for m in sorted(S) if abs(q-m*p)<=E] for p,q in combinations(sorted(vs),2)
            if any(abs(q-m*p)<=E for m in S)}

def canon(g,vs):
    blocks=[{v} for v in vs];tree=[]
    for (p,q),labels in sorted(g.items()):
        a=next(t for t in blocks if p in t);b=next(t for t in blocks if q in t)
        if a==b:continue
        blocks.remove(b);a.update(b);tree.append((p,q,labels[0]))
    assert len(blocks)==1
    return tree

def aggregate(vs,tree):
    x=min(vs);val={x:F(1)}
    for _ in vs:
        for p,q,m in tree:
            if p in val and q not in val:val[q]=val[p]*m
            if q in val and p not in val:val[p]=val[q]/m
    return prod(val.values())

x=100000007;y=1700000117
V=[2,3,5,7,11]
A=[200000033,300000031,500000041,700000031,1100000081]
B=[850000033,566666713,340000027,242857171,154545491]
vs=[x,y]+A+B
assert len(set(vs))==12 and all(prime(p) for p in vs)
N=prod(vs);L=N.bit_length();E=L
S=[p for p in range(2,L+1) if prime(p)]
g=graph(vs,S,E)
expected={(x,y,17)}|{(x,a,v) for a,v in zip(A,V)}|{(b,y,v) for b,v in zip(B,V)}
assert len(g)==11 and all(len(ms)==1 for ms in g.values())
tree=canon(g,vs)
assert set(tree)==expected and len({m for p,q,m in tree})==6
# Six different rational primes have six independent valuation vectors.
C=aggregate(vs,tree)
assert C==17**6 and x>4*L*E
j=x-40
while C*(j+1)**len(vs)<=N:j+=1
assert C*j**len(vs)<=N<C*(j+1)**len(vs)
print("unique-tree fixture: bits / vertices / edges / labels used",L,len(vs),len(g),len({m for p,q,m in tree}))
print("aggregate / exact floor center / signed offset / small-seed cutoff",int(C),j,x-j,4*L*E)
# Canonical predicate is deliberately different from 'there exists a tree'.
U=[31,61,167];S=[2,3,5,6,12];K=prod(U);g=graph(U,S,K.bit_length())
assert g[(31,167)]==[5,6]
canonical=canon(g,U);alternative=[(31,61,2),(61,167,3)]
assert all(m in g[p,q] for p,q,m in alternative)
assert aggregate(U,canonical)==10 and aggregate(U,alternative)==12
# v(10)=(1,0,1) along [2,3,5] is not proportional to
# any column of the dictionary; v(12) is a dictionary column.
print("canonical vs alternative aggregate",int(aggregate(U,canonical)),int(aggregate(U,alternative)))
