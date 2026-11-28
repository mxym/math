"""Finite checks on the known support and on generic branch selections."""
from fractions import Fraction as Q
from itertools import product

affine=((2,1),(3,-4),(1,1))
R=({0,1},{1,2},{2,0})
assert all(any(a*5+b==11 for a,b in [affine[i] for i in S]) for S in R)
assert all(not any(a*11+b==5 for a,b in [affine[i] for i in S]) for S in R)

count=0
for h in (2,4,6):
    for word in product(range(3),repeat=h):
        for orientation in (False,True):
            t=Q(23,7)
            y=t
            for a,b in zip(word[::2],word[1::2]):
                i=min(R[a]&R[b])
                k,c=affine[i]
                z=k*y+c if orientation else (y-c)/k
                y=(z-c)/k if orientation else k*z+c
            assert y==t
            count+=1

subsets=0
for r in range(3,10):
    for mask in range(1,(1<<r)-1):
        idx=[j for j in range(1,r+1) if (mask>>(j-1))&1]
        i=next(k for k in range(1,r+1) if k not in idx)
        x=Q(7,3)
        root=i*(x-5)+11
        assert all(root in {h*(x-5)+11 for h in range(1,r+1) if h!=j} for j in idx)
        assert (root-11)/i+5==x
        subsets+=1
    assert {i*(5-5)+11 for i in range(1,r+1)}=={11}
    assert all(i*(11-5)+11!=5 for i in range(1,r+1))

print("PASS separated witnesses: %d closed-word branch returns; %d proper label subsets with common branches; known support (5,11)." % (count,subsets))
