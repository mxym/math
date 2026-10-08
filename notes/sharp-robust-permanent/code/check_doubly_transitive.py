#!/usr/bin/env python3
"""Exact small-group replay for the doubly-transitive atom-TV theorem.

This checks the explicit extremizing measures on S_n, A_n, AGL(1,q).
The arbitrary finite 2-transitive group theorem is proved in paper.md.
Standard Python only; all probabilities use fractions.
"""
from fractions import Fraction as F
from itertools import permutations
from math import factorial


def parity(p):
    return sum(p[i]>p[j] for i in range(len(p))
               for j in range(i+1,len(p))) % 2


def aff(q):
    # q is prime here; the published theorem covers all prime powers.
    return [tuple((a*x+b)%q for x in range(q))
            for a in range(1,q) for b in range(q)]


def test_group(label, G):
    n=len(G[0])
    assert len(set(G))==len(G)
    identity=tuple(range(n))
    assert identity in G
    M_degree=min(sum(p[i]!=i for i in range(n)) for p in G if p!=identity)
    M={p for p in G if sum(p[i]!=i for i in range(n))==M_degree}
    D={p for p in G if all(p[i]!=i for i in range(n))}
    assert len(M)>0 and len(D)>0 and M_degree<n
    assert not (M & D) and identity not in M and identity not in D
    beta=F(n-M_degree,n)
    P={p:(beta if p==identity else F(0))+
         (F(M_degree,n*len(D)) if p in D else F(0)) for p in G}
    Q={p:F(1,len(M)) if p in M else F(0) for p in G}
    assert sum(P.values())==sum(Q.values())==1
    for i in range(n):
        for j in range(n):
            marg_p=sum(P[p] for p in G if p[i]==j)
            marg_q=sum(Q[p] for p in G if p[i]==j)
            assert marg_p==marg_q
            expected=beta if i==j else F(M_degree,n*(n-1))
            assert marg_p==expected
    delta=F(len(M),2*len(G))
    u=F(1,len(G))
    nu={p:u+delta*(P[p]-Q[p]) for p in G}
    assert min(nu.values())>=0 and sum(nu.values())==1
    for i in range(n):
        for j in range(n):
            assert sum(nu[p] for p in G if p[i]==j)==F(1,n)
    tv=sum(abs(nu[p]-u) for p in G)/2
    assert tv==delta
    assert nu[identity]==u+beta*delta
    print('PASS',label,'n',n,'order',len(G),'min-degree',M_degree,
          'D',len(D),'M',len(M),'sharp-coeff',beta)


def main():
    for n in (3,4,5):
        test_group('S%d'%n, list(permutations(range(n))))
    for n in (4,5,6):
        test_group('A%d'%n, [p for p in permutations(range(n)) if parity(p)==0])
    for q in (3,5,7):
        test_group('AGL(1,%d)'%q, aff(q))
    print('All exact finite 2-transitive group witnesses passed.')


if __name__=='__main__':
    main()
