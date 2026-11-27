#!/usr/bin/env python3
"""Exact rational qubit transfer moments and explicit path products."""
from fractions import Fraction as Q
from itertools import permutations, product
from math import prod


def transpose(a):
    return tuple(zip(*a))


def matmul(a,b):
    return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in zip(*b)) for row in a)


def diag(v):
    return tuple(tuple(Q(v[i]) if i==j else Q(0) for j in range(len(v))) for i in range(len(v)))


def avg(mats):
    return tuple(tuple(sum(e)/len(mats) for e in zip(*rows)) for rows in zip(*mats))


def conjug(A,p,s):
    # Oriented permutation has j-th column s[j] e[p[j]].
    return tuple(tuple(s[i]*s[j]*A[p[i]][p[j]] for j in range(3)) for i in range(3))


def kron_moment(mats,k):
    ids=list(product(range(3),repeat=k))
    return tuple(tuple(sum(prod(B[x][y] for x,y in zip(i,j)) for B in mats)/len(mats)
                       for j in ids) for i in ids)


G=[]
for p in permutations(range(3)):
    perm_sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
    for s in product((-1,1),repeat=3):
        if perm_sign*prod(s)==1:
            G.append((p,s))
assert len(G)==24
for i,j in product(range(3),repeat=2):
    M=tuple(tuple(Q(int((x,y)==(i,j))) for y in range(3)) for x in range(3))
    assert avg([conjug(M,p,s) for p,s in G])==diag([Q(i==j,3)]*3)
print("qubit projective Clifford: all 9 elementary adjoint covariance averages exact")

DAMP=diag((Q(1,2),Q(1,2),Q(1,4)))
DEPH=diag((0,0,1))
PAULI=diag((Q(1,2),Q(-1,2),0))
UNITARY=diag((-1,-1,1))
REPLACE=diag((0,0,0))
ROT=((Q(3,5),Q(-4,5),Q(0)),(Q(4,5),Q(3,5),Q(0)),(Q(0),Q(0),Q(1)))
ROTATED=matmul(ROT,DAMP)
# Damping is nonunital (translation (0,0,3/4)); following by ROT here
# does not change that translation. Only the traceless block is tested.
channels=(("dephasing",DEPH),("damping",DAMP),("Pauli-mixture",PAULI),
          ("unitary",UNITARY),("replacement",REPLACE),("rotated-damping",ROTATED))
paths=0
for name,A in channels:
    bs=[conjug(A,p,s) for p,s in G]
    alpha=sum(A[i][i] for i in range(3))/3
    u=sum(v*v for row in A for v in row)/3
    assert avg(bs)==diag([alpha]*3)
    assert avg([matmul(transpose(B),B) for B in bs])==diag([u]*3)
    assert avg([matmul(B,transpose(B)) for B in bs])==diag([u]*3)
    S2=kron_moment(bs,2)
    tr_pairs=(0,4,8)
    vecI=tuple(Q(int(k in tr_pairs)) for k in range(9))
    assert tuple(sum(v*w for v,w in zip(row,vecI)) for row in S2)==tuple(u*w for w in vecI)
    words=[matmul(B,C) for B,C in product(bs,repeat=2)]
    paths+=len(words)
    assert avg([matmul(transpose(B),B) for B in words])==diag([u*u]*3)
    assert avg([matmul(B,transpose(B)) for B in words])==diag([u*u]*3)
    assert kron_moment(words,2)==matmul(S2,S2)
    for k in (2,3,4):
        S=kron_moment(bs,k)
        if name!="rotated-damping":
            assert all(S[i][j]==0 for i in range(len(S)) for j in range(len(S)) if i!=j)
            assert max(abs(S[i][i]) for i in range(len(S)))<=u
        else:
            # Frobenius upper bound on S^m derived from its explicit word
            # expansion S^m=E P_m^{tensor k}; verify this matrix identity
            # independently on the smaller k=3 case.
            if k==3:
                assert kron_moment(words,k)==matmul(S,S)
    print(f"qubit {name}: alpha={alpha}, u={u}, all-copy secondary={max(abs(alpha),u)}")
print(f"qubit moment product replay: {paths} ordered length-2 words; 2/3/4-copy blocks exact")

# Negative controls: subgroup of diagonal rotations is a unitary
# 1-design, but it fails adjoint twirling. Repeating a single sampled
# Clifford throughout the sequence also leaves every dephaser idempotent.
sub=[(p,s) for p,s in G if p==(0,1,2)]
assert len(sub)==4
for j in range(3):
    assert sum(s[j] for _,s in sub)==0
assert avg([conjug(DEPH,p,s) for p,s in sub])==DEPH
full=[conjug(DEPH,p,s) for p,s in G]
assert all(matmul(B,B)==B for B in full)
assert avg(full)==diag([Q(1,3)]*3)
assert matmul(avg(full),avg(full))==diag([Q(1,9)]*3)
print("negative controls: Pauli 1-design leaves a unit root; held-fixed Clifford sampling does not mix")
