#!/usr/bin/env python3
"""Exact 2396 Hadamard orbit-sum classification and multiplier restrictions."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product

P = 599
N = 4*P
PERMS = tuple(permutations(range(4)))
SIGNS = tuple(product((1,-1),repeat=4))


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def positive_first(row):
    return row if row[0]>0 else tuple(-x for x in row)


def transform(a,p,s):
    return tuple(a[i]*t for i,t in zip(p,s))


def canonical(M):
    # A first row is picked among all rows; arrange its absolute entries
    # increasingly and make it positive. For ties every column order is tried.
    choices=[]
    for j,r in enumerate(M):
        for p in PERMS:
            line=tuple(abs(r[i]) for i in p)
            if any(a>b for a,b in zip(line,line[1:])):
                continue
            s=tuple(1 if r[i]>0 else -1 for i in p)
            tail=sorted(positive_first(transform(q,p,s)) for k,q in enumerate(M) if k!=j)
            choices.append((line,*tail))
    return min(choices)


def quat(vals):
    a,b,c,d=vals
    return ((a,-b,-c,-d),(b,a,-d,c),(c,d,a,-b),(d,-c,b,a))


def transpose(T):
    return tuple(zip(*T))


def monomial_order(T):
    p,s=T
    q,r=p,s
    n=1
    while (q,r)!=(tuple(range(4)),(1,1,1,1)):
        q,r=tuple(q[i] for i in p),tuple(r[i]*t for i,t in zip(p,s))
        n+=1
        assert n<=24
    return n


def automorphism_orders(M):
    # A column monomial map determines its row partner uniquely.
    rows={positive_first(r) for r in M}
    return sorted(monomial_order((p,s))
          for p in PERMS for s in SIGNS
          if {positive_first(transform(r,p,s)) for r in M}==rows)


def main():
    assert all(P%d for d in range(2,25))
    assert P-1==2*13*23
    vals=tuple(range(1,49,2))
    types=[r for r in combinations_with_replacement(vals,4) if dot(r,r)==N]
    vecs={positive_first(transform(r,p,s)) for r in types for p in PERMS for s in SIGNS}
    assert len(types)==28 and len(vecs)==4800
    orbit_matrices=set()
    counts=Counter()
    for r in types:
        orth=[q for q in vecs if dot(r,q)==0]
        local=[]
        for a,b,c in combinations(orth,3):
            if dot(a,b)==dot(a,c)==dot(b,c)==0:
                local.append((r,a,b,c))
        counts[len(orth),len(local)]+=1
        orbit_matrices.update(map(canonical,local))
    expected={canonical(M) for r in types for M in (quat(r),transpose(quat(r)))}
    assert counts=={(6,2):28}
    assert orbit_matrices==expected and len(expected)==50
    assert Counter(len({canonical(quat(r)),canonical(transpose(quat(r)))}) for r in types)=={1:6,2:22}
    for M in expected:
        assert automorphism_orders(M)==[1,2]+[4]*6
        for i,a in enumerate(M):
            for j,b in enumerate(M):
                assert dot(a,b)==(N if i==j else 0)
    for ell in (13,23):
        possible={x for x in vals if x%(2*ell) in (1,2*ell-1)}
        assert possible==({1,25,27} if ell==13 else {1,45,47})
        assert all(dot(row,row)!=N for row in combinations_with_replacement(sorted(possible),4))
    print("PASS: 28 types, 56 normalized charts, 50 orbit-sum classes; all quaternion stabilizers")
    print("PASS: multiplier orders 13 and 23 fail the signed row-sum equation")


if __name__ == "__main__":
    main()
