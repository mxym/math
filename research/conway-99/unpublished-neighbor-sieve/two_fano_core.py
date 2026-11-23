"""Unique 24-site signed-support union for orthogonal Fano lines."""
from itertools import product, combinations
V=range(24)
blocks=[set(range(i,i+5)) for i in (4,9,14,19)]
sides=[a|b for a,b in zip(({0,1},{2,3},{0,2},{1,3}),blocks)]
def labeled(mask):
    N=[set() for _ in V]
    def add(i,j):
        N[i].add(j);N[j].add(i)
    ns=(2,1,3,4,5,6,7)
    for a,b in ((0,1),(2,3)):
        for t,x in enumerate(sorted(sides[a]),1):
            for n,y in zip(ns,sorted(sides[b])):
                if (t&n).bit_count()%2:add(x,y)
    for k,(a,b) in enumerate(product((0,1),(2,3))):
        aa=[x for x in sorted(blocks[a]) if not N[x]&sides[b]]
        bb=[y for y in sorted(blocks[b]) if not N[y]&sides[a]]
        assert len(aa)==len(bb)==2
        for x,y in zip(aa,bb[::-1] if mask>>k&1 else bb):add(x,y)
    return N
def check():
    allowed=[]
    for mask in range(16):
        N=labeled(mask)
        if any(len(N[i]&N[j])>2-(j in N[i]) for i,j in combinations(V,2)):continue
        allowed.append(mask)
    assert allowed==[15]
    N=labeled(15)
    def safe(x,j):
        if x in sides[j]|sides[j+1]:return True
        p,=N[x]&sides[j]
        n,=N[x]&sides[j+1]
        return n in N[p]
    good=[x for x in V if safe(x,0) and safe(x,2)]
    assert good==[0,1,2,3,5,10,15,20]
    for i,j in ((0,3),(1,2)):assert j in N[i] and not N[i]&N[j]
    print("16 signed charts; unique survivor 15; 8 jointly safe in core, 2 distinct forced safe caps outside.")
if __name__=='__main__':check()
