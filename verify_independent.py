#!/usr/bin/env python3
"""Check exact support feasibility by rational linear algebra, not tensor expansion."""
from itertools import combinations, product
from math import gcd


def primitive(vec):
    g = gcd(*vec)
    return tuple(v//g for v in vec) if g>1 else tuple(vec)


def reduce(vec,basis):
    for pivot, row in basis:
        s=vec[pivot]
        if s:
            p=row[pivot]
            vec=primitive([p*a-s*b for a,b in zip(vec,row)])
    return vec


def basis_of(rows,d):
    out=[]
    for v in rows:
        v=reduce(v,out)
        for p,a in enumerate(v):
            if a:
                out.append((p,v))
                out.sort()
                break
        if len(out)==d:
            break
    return out


def walsh(x,y):
    return -1 if (x&y).bit_count()%2 else 1


def direct_can(n,small,large,S,H=None):
    cols=[a for a in range(1<<n) if a.bit_count() in (small,large)]
    mat=[tuple(walsh(x,y) for y in cols) for x in range(1<<n)] if H is None else H
    basis=basis_of((r for i,r in enumerate(mat) if i not in S),len(cols))
    if len(basis)==len(cols): return False
    if any(not any(reduce(mat[x],basis)) for x in S): return False
    # An allowed coefficient vector must avoid both constraints that make
    # one complete level zero. Over Q, finite unions of proper hyperplanes
    # cannot cover a vector space; so separate nonzero witnesses suffice.
    return all(any(any(reduce(tuple(int(a==b) for b in range(len(cols))),basis))
                   for a,C in enumerate(cols) if C.bit_count()==lev)
               for lev in (small,large))


def all_partition_pairs(indices,k):
    if k==0:
        yield ()
        return
    a,*others=indices
    if len(others)>=2*k:
        yield from all_partition_pairs(others,k)
    for nr,b in enumerate(others):
        for rest in all_partition_pairs(others[:nr]+others[nr+1:],k-1):
            yield ((a,b),)+rest


def expected_masks(n,i,j):
    if i+j>n: i,j=n-j,n-i
    m=n-2*i
    if m>4: raise ValueError('tiny exhaustive test only')
    W=list(range(1<<m))
    gsets=[]
    for pos in combinations(W,1<<(m-1)):
        q=set(pos)
        if all(sum(walsh(x,y)*(1 if x in q else -1) for x in W)==0
               for y in W if y.bit_count()!=j-i):
            gsets.append(q)
    result=set()
    for v in all_partition_pairs(list(range(n)),i):
        free=[x for x in range(n) if all(x not in p for p in v)]
        for mask in product((0,1),repeat=i):
            for S in gsets:
                result.add(tuple(x for x in range(1<<n)
                                 if all(((x>>a)^(x>>b))&1==u for (a,b),u in zip(v,mask))
                                 and sum((x>>a&1)<<b for b,a in enumerate(free)) in S))
    return result


def check(n,i,j):
    size=1<<(max(n-i,j)-1)
    U=list(range(1<<n))
    H=[tuple(walsh(x,y) for y in U if y.bit_count() in (i,j)) for x in U]
    tested=0
    sat=set()
    for r in range(1,size+1):
        for T in combinations(U,r):
            tested+=1
            if direct_can(n,i,j,set(T),H):
                assert r==size
                sat.add(T)
    assert sat==expected_masks(n,i,j), (n,i,j,sat,expected_masks(n,i,j))
    return tested,len(sat)


def main():
    all_cases=[(n,i,j) for n in range(1,4) for i in range(n+1)
               for j in range(i+1,n+1,2)]
    all_cases.extend(((4,0,3),(4,1,2),(4,2,3)))
    rows=[(n,i,j,*check(n,i,j)) for n,i,j in all_cases]
    print('exact support rank checks by (n,i,j,candidate masks,minimizing masks):')
    for row in rows:
        print(' '.join(map(str,row)))
    print(f'{sum(r[3] for r in rows)} masks; all exact minima and all minimizer support families matched')
    # Feasibility with one Fourier component accidentally zero must not
    # count. At n=2, a function supported at z_1=z_2 has constant+level2
    # spectrum, and cannot have only the two requested levels 0 and 1.
    assert not direct_can(2,0,1,{0,3})
    print('PASS exact rank, full-support feasibility, and independent support classification')


if __name__=='__main__': main()
