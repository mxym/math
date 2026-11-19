from collections import Counter
from itertools import product
from math import prod
nums=[1,1]+[2]*7; dens=[4,4]+[5]*7; signs=[1]+[-1]*8
B=10
den=prod(dens)**3
def Q(coeff):
    # Independent tiny polynomials, indexed by physical decimal power.
    C=[Counter({0:1}) for _ in range(10)]
    for k,c in enumerate(coeff):
        shift=1 if abs(c)==10 else 0
        for i,(p,q,s) in enumerate(zip(nums,dens,signs)):
            h=i+shift
            z=Counter()
            for y,w in C[h].items():
                z[y]+=(q-p)*w
                z[y+((1 if c>0 else -1)*s)]+=p*w
            C[h]=z
    assert all(max(c)-min(c)<=3 for c in C)
    return prod(max(c.values()) for c in C), sum(max(c,key=c.get)*B**i for i,c in enumerate(C)), max(max(c)-min(c) for c in C)
for c in [(1,1,1),(1,1,-1),(1,1,10)]:
    a=Q(c)
    print(c,a,den)
assert max(Q((1,1,1))[0],Q((1,1,-1))[0])<Q((1,1,10))[0]
