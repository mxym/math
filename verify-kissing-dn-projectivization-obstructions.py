#!/usr/bin/env python3
"""Independent obstruction census. Requires Python >=3.10 and NumPy.
No solver, tolerance, precomputed certificate, or case table is used.
Use signed half-grid in [-3/2,3/2]^n for 2<=n<=6. After clipping the
polar to that cube, fixed coordinates/signed tight edges give half-grid
vertices. Any outside vertex produces a nonroot feasible equatorial
point by a slight interior perturbation then radial projection. For a
nonroot x on the equatorial sphere either max |x_i|>1 or sum |x_i|>2,
since sum x_i^2 <= max |x_i| sum |x_i|, with equality at both bounds
only for roots. Opposite signed coordinate or half-sign-cube testers
then violate the lower bound. If no outside vertex, concavity reduces
to all inside grid pairs. This independently checks all subsets at once.
"""
import numpy as np
from itertools import combinations, product

for n in range(2,7):
    def root(i,j,a,b):
        return tuple(a if k==i else b if k==j else 0 for k in range(n))
    R=[root(i,j,a,b) for i,j in combinations(range(n),2)
       for a,b in product([1,-1],repeat=2)]
    index={r:i for i,r in enumerate(R)}
    def mask(roots):
        return sum(1<<index[r] for r in roots)
    W=np.array(list(product(range(-3,4),repeat=n)),dtype=np.int16)
    l2=(W*W).sum(axis=1)
    weights=np.uint64(1)<<np.arange(len(R),dtype=np.uint64)
    B=(W@np.array(R,dtype=np.int16).T>2)@weights
    masks=set(map(int,B[l2>8]))
    W,B,l2=W[l2<=8],B[l2<=8],l2[l2<=8]
    for i,w in enumerate(W):
        d=w@W[:i].T
        failure=(d<-4)&((d+4)**2>(8-l2[i])*(8-l2[:i]))
        masks.update(map(int,B[i]|B[:i][failure]))
    todo=np.array(sorted(masks,key=lambda m:(m.bit_count(),m)),dtype=np.uint64)
    minimal=set()
    while len(todo):
        m=todo[0];minimal.add(int(m));todo=todo[(todo&m)!=m]
    predicted=set()
    if n>=3:
        for r in R:predicted.add(mask((r,tuple(-t for t in r))))
    if n>=4:
        for i,j,k in combinations(range(n),3):
            for a,b,c in product([1,-1],repeat=3):
                predicted.add(mask((root(i,j,a,b),root(j,k,b,c),root(i,k,a,c))))
    q=min(4,n-1)
    for i,a in product(range(n),[1,-1]):
        for J in combinations([j for j in range(n) if j!=i],q):
            for signs in product([1,-1],repeat=q):
                predicted.add(mask(root(i,j,a,b) for j,b in zip(J,signs)))
    if minimal!=predicted:
        raise AssertionError((n,minimal-predicted,predicted-minimal))
    print('rank',n,'minimal labelled defect masks',len(minimal),'PASS')
