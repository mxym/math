#!/usr/bin/env python3
"""Check the six-layer dyadic-cycle obstruction for regular covers of K_{3,3}."""
from itertools import product, combinations

LEFT = range(3)
RIGHT = range(3,6)
Z = (0,0,0,0)
VOLTAGES = {}
for a,b in product(LEFT,RIGHT):
    v = Z if a==0 or b==3 else tuple(int(i==2*(a-1)+b-4) for i in range(4))
    VOLTAGES[a,b] = v
    VOLTAGES[b,a] = tuple(-x for x in v)


def add(x,y):
    return tuple(a+b for a,b in zip(x,y))


def check_short(L):
    count = 0
    def rec(path,x):
        nonlocal count
        a = path[-1]
        if len(path)==L:
            b = path[0]
            if (a,b) not in VOLTAGES or a==path[1] or path[-2]==b:
                return
            v = add(x,VOLTAGES[a,b])
            assert any(v),path
            assert any(t%5 for t in v),path
            count += 1
            return
        for b in RIGHT if a in LEFT else LEFT:
            if len(path)<2 or b!=path[-2]:
                rec([*path,b],add(x,VOLTAGES[a,b]))
    for a in range(6):
        rec([a],Z)
    return count


def check_witness():
    choices = [int(t)+3 for t in "0101012010201212"]
    route = [0]
    for i,b in enumerate(choices):
        route.extend([b,1-i%2])
    assert len(route)==33
    chain = [(0,Z)]
    x = Z
    for a,b in zip(route,route[1:]):
        x = add(x,VOLTAGES[a,b])
        chain.append((b,x))
    assert chain[0] == chain[-1]
    assert len(set(chain[:-1]))==32
    assert len({(a,tuple(t%5 for t in y)) for a,y in chain[:-1]})==32
    for (a,x),(b,y) in combinations(chain[:-1],2):
        if a == b:
            v = tuple(u-t for u,t in zip(x,y))
            assert any(v) and all(abs(t)<=32 for t in v)
            w = sum(t*65**i for i,t in enumerate(v))
            assert 0 < abs(w) < 32*sum(65**i for i in range(4))+1


def main():
    counts = [check_short(L) for L in (4,8,16)]
    assert counts == [72,648,133128]
    check_witness()
    print("PASS",counts,"short rooted directed base walks, and the simple 32-cycle")


if __name__ == "__main__":
    main()
