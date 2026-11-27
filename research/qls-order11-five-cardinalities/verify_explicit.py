#!/usr/bin/env python3
"""Independent exact Gram and ray checks with integer quadratic-field pairs."""
from collections import Counter
from itertools import combinations, product

U = range(11)
D = {1,3,4,5,9}
assert D == {x for x in U if pow(x,5,11)==1}
# The first representative for each cardinality, plus a second 119 witness.
SIG = {
    66: (0,1,2,3,4,5,6,7,8,9,10),
    105:(0,1,2,3,4,5,6,7,8,10,9),
    106:(0,1,2,3,8,5,9,10,4,6,7),
    113:(0,1,2,3,5,9,7,6,10,4,8),
    115:(0,1,2,3,4,5,7,6,10,9,8),
    116:(0,1,2,3,4,5,6,8,7,10,9),
    117:(0,1,2,3,4,5,6,7,9,10,8),
    118:(0,1,2,3,4,5,7,6,8,10,9),
    119:(0,1,2,3,4,5,8,9,10,7,6),
    120:(0,1,2,3,4,5,6,8,9,10,7),
    121:(0,1,2,3,4,5,7,8,6,10,9),
}
SECOND = (1,10,9,8,4,2,3,0,5,7,6)

def mul(x,y):
    a,b=x
    c,d=y
    return a*c-11*b*d,a*d+b*c

def bar(x):
    return x[0],-x[1]

I,Z=(6,0),(-5,1)
assert mul(Z,bar(Z))==mul(I,I)==(36,0)
def phase(x):
    return Z if x%11 in D else I

def check(want,s,second=False):
    assert sorted(s)==list(U)
    V={(a,b):tuple(mul(phase(k-a),phase(s[k]-b)) for k in U)
              for a,b in product(U,repeat=2)}
    # Every coordinate in V is multiplied by 36*sqrt(11) vs the unit vector.
    checked=0
    for axis in (0,1):
        for a in U:
            row=[V[a,b] if axis==0 else V[b,a] for b in U]
            for m in U:
                for n in range(m,11):
                    prod=[mul(bar(x),y) for x,y in zip(row[m],row[n])]
                    colsum=tuple(map(sum,zip(*prod)))
                    assert colsum==((11*36**2,0) if m==n else (0,0))
                    checked+=1
    assert checked==1452
    signatures={}
    for ij,c in V.items():
        assert mul(c[0],bar(c[0]))==(36**2,0)
        signatures[ij]=tuple(mul(x,bar(c[0])) for x in c)
    # Transitive grouping and direct all-pair coverage are both tested.
    groups={}
    for c,v in signatures.items():
        groups.setdefault(v,[]).append(c)
    assert len(groups)==want
    predicted=sorted(tuple(g) for cs in groups.values() for g in combinations(cs,2))
    allpairs=list(combinations(V,2))
    assert len(allpairs)==7260
    witnessed=[(s,t) for s,t in allpairs if signatures[s]==signatures[t]]
    assert predicted==witnessed
    hist=sorted(Counter(map(len,groups.values())).items())
    if second:
        assert witnessed==[((2,1),(7,10)),((4,3),(6,4))]
        assert hist==[(1,117),(2,2)]
        print(f'second {want}: multiplicities {hist}; repeated pairs {witnessed}')
    else:
        print(f'{want}: multiplicities {hist}; equal unordered pairs {len(witnessed)}')
    return hist

if __name__=="__main__":
    print("direct exact checks: 22 bases / 1452 Gram entries and 7260 cell pairs each")
    for c,s in SIG.items():
        check(c,s)
    check(119,SECOND,second=True)
    altered = list(SECOND)
    altered[0], altered[1] = altered[1], altered[0]
    print('negative control: exchanging the first two images in the second 119 witness')
    assert check(121,altered)==[(1,121)]
