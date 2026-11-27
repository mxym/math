#!/usr/bin/env python3
"""Exhaustive small cases of Q6.7 in two independently specified GF bases."""
from hashlib import sha256

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

CASES = {
    (4,285): None, (4,299): None,
    (5,1033): (86,771,366), (5,1051): (10,305,972),
    (7,16427): (9,4147,14067), (7,16441): (7,2633,10911),
    (8,65581): (14,14512,17878), (8,65593): (9,11760,20972),
}
LUT_HASH = {
    285:"e40b8c5ae7daf8321e0ec182d169eec921964f029df1b7a786eaa40b86c8b49e",
    299:"48bd814934d4a186c9908baa40a327d844a31ea9d9dd1ddc142a8530e127aa78",
}
IMAGES = {4:256,5:709,7:10693,8:42064}
SIEVE = {4:0,5:15,7:1092,8:4224}

def check(e,m,witness):
    Q=1<<(2*e)
    log=[-1]*Q
    exp=[]
    v=1
    for i in range(Q-1):
        assert v and log[v]==-1
        log[v]=i
        exp.append(v)
        v<<=1
        if v&Q:
            v^=m
    # Nonzero power cycle has full size, certifying irreducibility as well.
    assert v==1 and all(t>=0 for t in log[1:])
    def power(x,n):
        return exp[log[x]*n%(Q-1)] if x else 0
    def mul(x,y):
        return exp[(log[x]+log[y])%(Q-1)] if x and y else 0
    def T(x):
        z=0
        for i in range(e):
            z^=power(x,4**i)
        return z
    def V(x):
        return x^power(x,4)^power(x,16)
    def D(x):
        return 1^power(x,9)^power(x,21)^power(x,33)^power(x,45)
    trace=[T(x) for x in range(Q)]
    tab=[power(V(x),2)^mul(mul(trace[x],trace[x]^x),D(x)) for x in range(Q)]
    assert len(set(power(V(x),2) for x in range(Q)))==Q
    image=len(set(tab))
    good=[x for x in range(Q) if trace[x]==1 and trace[mul(1^x,D(x))]==1]
    assert image==IMAGES[e] and len(good)==SIEVE[e]
    if witness is None:
        assert set(tab)==set(range(Q))
        h=sha256(bytes(tab)).hexdigest()
        assert h==LUT_HASH[m]
        print(f"e={e} modulus={m}: all {Q} outputs distinct; LUT SHA256 {h}")
    else:
        x,w,z=witness
        assert x==good[0] and x!=w and trace[x]==1 and trace[w]==trace[z]==0
        assert tab[x]==tab[w]==z
        print(f"e={e} modulus={m}: image={image}/{Q}, sieve={len(good)}, "
              f"(x,w,g(x))=({x},{w},{z}) PASS")

if __name__=="__main__":
    for (e,m),witness in CASES.items():
        check(e,m,witness)
    print("PASS exact small field tables and trace-collision certificates")
