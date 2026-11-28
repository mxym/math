#!/usr/bin/env python3
"""Rational frame, signed-deficit, and finite constant tests."""
from fractions import Fraction as F
from itertools import product


def eye(n):
    return [[F(int(i==j)) for j in range(n)] for i in range(n)]


def transpose(A):
    return list(map(list, zip(*A)))


def mm(A,B):
    BT=transpose(B)
    return [[sum(x*y for x,y in zip(u,v)) for v in BT] for u in A]


def scale(c,A):
    return [[c*x for x in row] for row in A]


def add(A,B):
    return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]


def diff(A,B):
    return add(A,scale(-1,B))


def outer(a,b):
    return [[x*y for y in b] for x in a]


def gram(A,B):
    return sum(x*y for a,b in zip(A,B) for x,y in zip(a,b))


def trace(A):
    return sum(A[j][j] for j in range(len(A)))


def comm(A,B):
    return diff(mm(A,B),mm(B,A))


def tp_map(K,A):
    z=scale(0,A)
    for k in K:
        z=add(z,mm(mm(k,A),transpose(k)))
    return z


def positive_ldl(M):
    A=[r[:] for r in M]
    for j in range(len(A)):
        d=A[j][j]
        assert d>0
        for k in range(j+1,len(A)):
            for i in range(j+1,len(A)):
                A[k][i]-=A[k][j]*A[j][i]/d


b=[list(x) for x in zip(*eye(4))]
v=[[x+1 for x in e] for e in b]
w=[[5*x-1 for x in e] for e in b]
P=[scale(F(1,7),outer(x,x)) for x in v]
M=[scale(F(7,25),outer(x,x)) for x in w]
assert all(mm(mm(P[i],M[j]),P[i])==scale(int(i==j),P[i])
           for i,j in product(range(4),repeat=2))
B0=scale(0,eye(4))
A0=scale(0,eye(4))
for q,N in enumerate(M,1):
    B0=add(B0,N)
    A0=add(A0,scale(q,N))
assert trace(B0)==F(532,25) and trace(A0)==F(266,5)
for i in range(4):
    assert mm(diff(A0,scale(i+1,B0)),[[x] for x in v[i]])==[[0]]*4
    assert mm(P[i],P[i])==P[i]
print("exact rational frame: 16 dual compressions, 4 pencil kernels, both trace normalizations")

I=eye(4)
units=[outer(a,b) for a,b in product(eye(4),repeat=2)]
cols=[[comm(p,x) for p in P] for x in units]
U=[[sum(gram(a,b) for a,b in zip(x,y))+trace(ex)*trace(ey)/4
    for y,ey in zip(cols,units)] for x,ex in zip(cols,units)]
gammaF=F(36,595)
positive_ldl(diff(U,scale(gammaF,eye(16))))
print("exact rational LDL: fixed-frame commutator gap at least 36/595 off the scalars")

# An explicit trace-preserving but not unital, rank-one Kraus channel.
e=eye(3)
K=[outer(e[0],e[0]),outer(e[0],e[1]),outer(e[2],e[2])]
adj=[transpose(k) for k in K]
assert tp_map(adj,eye(3))==eye(3) and tp_map(K,eye(3))!=eye(3)
cnt=0
for signs in product((-1,1),repeat=3):
    S=[[x*signs[i] for x in e[i]] for i in range(3)]
    T=tp_map(adj,S)
    Q=diff(eye(3),scale(F(1,2),add(mm(S,T),mm(T,S))))
    ksum=sum(gram(comm(k,S),comm(k,S)) for k in K)
    assert ksum==2*trace(Q)
    for d in [(1,1,1),(1,3,7),(5,2,1)]:
        Abs=[[x*d[i] for x in e[i]] for i in range(3)]
        Delta=mm(S,Abs)
        lhs=trace(mm(S,diff(Delta,tp_map(K,Delta))))
        assert lhs==trace(mm(Abs,Q)) and lhs>=min(d)*ksum/2
        cnt+=1
print(f"exact nonunital Kraus witness: {cnt} signed deficits and trace-gap inequalities")

mu,g,J=F(7,25),F(1,15000),12
kappa=F(1,10**10)
witness_scale=4*mu*kappa/trace(A0)
gamma_actual=g/4
C0=75; M0=21
rotation=2*C0**2*M0+2*C0*M0
error=rotation/mu+2*M0/mu+2*C0
assert error==855300 and error<10**6
assert kappa<=mu/(2*M0) and kappa<=F(1,4) and 4*J*(10**6*kappa)**2<=g/4
assert witness_scale==2*kappa/95
assert witness_scale*gamma_actual/(2*4*J) >= F(1,10**19)
assert 1/(2*gammaF)<9 and 9+49*(2+32*9)<15000
print("exact absolute constants: 12 thresholds, kappa=1e-10, trace bound 1e-19")
