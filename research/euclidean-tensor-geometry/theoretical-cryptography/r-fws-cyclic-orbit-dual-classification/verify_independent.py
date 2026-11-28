#!/usr/bin/env python3
"""Independent F4[x] tower, ranks, and absolute trace from matrices."""
from collections import Counter
from itertools import product


K=range(4)
# GF(4) in basis 1,w. Multiplication table, not bit-polynomial reduction.
F4=((0,0,0,0), (0,1,2,3), (0,2,3,1), (0,3,1,2))


def prod4(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]^=F4[x][y]
    return c


def remainder(a,f):
    a=list(a)
    assert f[-1]==1
    while len(a)>=len(f):
        h=len(a)-len(f)
        u=a[-1]
        for i,v in enumerate(f[:-1]):
            a[h+i]^=F4[u][v]
        a.pop()
    return tuple(a)


def find_quartic():
    bad=set()
    for i in (1,2):
        for f,g in product(product(K,repeat=i),product(K,repeat=4-i)):
            bad.add(tuple(prod4(f+(1,),g+(1,))))
    return next(f+(1,) for f in product(K,repeat=4) if f+(1,) not in bad)


def enc(a):
    return sum(x<<(2*i) for i,x in enumerate(a))


def dec(a):
    return tuple((a>>(2*i))&3 for i in range(4))


def echelon(vectors):
    base={}
    for a in vectors:
        while a:
            b=a.bit_length()-1
            if b not in base:
                base[b]=a
                break
            a ^= base[b]
    return tuple(base.values())


def run():
    f=find_quartic()
    assert len(f)==5
    def mul(a,b):
        return enc(remainder(prod4(dec(a),dec(b)),f))
    M=tuple(tuple(mul(a,b) for b in range(256)) for a in range(256))
    assert all(set(row)==set(range(256)) for row in M[1:])
    b8=tuple(1<<i for i in range(8))
    # Field trace computed as ordinary matrix trace of multiplication,
    # not via the Frobenius sum used by the first checker.
    trace=tuple(sum((row[v]>>i)&1 for i,v in enumerate(b8))%2 for row in M)
    U=(1,2,4)
    S=echelon(a for a in range(256) if not any(trace[M[a][u]] for u in U))
    assert len(S)==5
    perpK=echelon(a for a in range(256) if not (trace[a] or trace[M[a][2]]))
    assert len(perpK)==6 and len(echelon(S+tuple(M[2][v] for v in S)))==6
    assert len(echelon(S+perpK))==6
    hist=Counter()
    for a in range(1,256):
        d1=2*(len(echelon(U+tuple(M[a][v] for v in U)))-len(U))
        d2=2*(len(echelon(S+tuple(M[a][v] for v in S)))-len(S))
        assert d1==d2
        if d2==2:
            assert a in (2,3)
        hist[d2]+=1
    assert hist=={0:1,2:2,4:36,6:216}

    # Check the adjoint identity with a non-multiplier linear transvection.
    def trans(u):
        return u^((u&1)<<1)
    Tad=[next(y for y in range(256) if all(trace[M[trans(x)][z]]==
          trace[M[x][y]] for x in b8)) for z in range(256)]
    assert len(set(Tad))==256
    TU=tuple(trans(u) for u in U)
    left={v for v in range(256) if all(not trace[M[v][u]] for u in TU)}
    right={v for v in range(256) if all(not trace[M[Tad[v]][u]] for u in U)}
    assert left==right and len(left)==32
    print(f"INDEPENDENT: F4 tower modulus constant-first {f}, 255 rank-based same-multiplier distances; trace-adjoint identity PASS")


if __name__=="__main__":
    run()
