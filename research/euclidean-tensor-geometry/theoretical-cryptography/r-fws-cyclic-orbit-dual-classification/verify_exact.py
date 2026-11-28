#!/usr/bin/env python3
"""Bit-polynomial field, explicit translates, and small Grassmannians."""
from collections import Counter


def mod(a,f):
    while a and a.bit_length()>=f.bit_length():
        a ^= f<<(a.bit_length()-f.bit_length())
    return a


def tables(f):
    n=f.bit_length()-1
    for d in range(1,n//2+1):
        assert all(mod(f,g) for g in range(1<<d,1<<(d+1)))
    Q=1<<n
    def mul(a,b):
        c=0
        while b:
            if b&1:
                c ^= a
            a <<= 1
            b >>= 1
        return mod(c,f)
    M=tuple(tuple(mul(a,b) for b in range(Q)) for a in range(Q))
    def tr(a):
        b=0
        for _ in range(n):
            b ^= a
            a=M[a][a]
        assert b in (0,1)
        return b
    trace=tuple(tr(a) for a in range(Q))
    def dual(U):
        return frozenset(a for a in range(Q) if not any(trace[M[a][u]] for u in U))
    return n,Q,M,dual


def code(U,M):
    return {frozenset(row[u] for u in U) for row in M[1:]}


def rowdist(U,C):
    return Counter(2*(len(U).bit_length()-len(U&W).bit_length()) for W in C)


def witness():
    n,Q,M,dual=tables(0x11d)
    K=frozenset(x for x in range(Q) if M[M[x][x]][M[x][x]]==x)
    lam=2
    assert len(K)==4
    U=K|frozenset(x^lam for x in K)
    S=dual(U)
    assert (len(U),len(S))==(8,32) and dual(S)==U
    assert len(code(U,M))==len(code(S,M))==255
    dist={0:1,2:2,4:36,6:216}
    assert rowdist(U,code(U,M))==rowdist(S,code(S,M))==dist
    vals={a for a in range(1,Q) if len(S&{M[a][s] for s in S})==16}
    assert vals==K-{0,1}
    T=dual(K)
    assert len(T)==64 and S<T and all(M[a][s] in T for a in K for s in T)
    assert {a^M[min(vals)][b] for a in S for b in S}==T
    print("EXACT: polynomial 0x11d binary witness, orbit distance counts 1/2/36/216; all distance-two scalars in F4; F4-span dimension 3")


def all_subspaces(Q,n):
    subs={frozenset({0})}
    for h in range(n+1):
        yield h,subs
        if h<n:
            subs={U|frozenset(u^v for u in U) for U in subs for v in range(1,Q) if v not in U}


def small_graphs():
    count=fws=0
    for f in (0x7,0xb,0x13,0x25):
        n,Q,M,dual=tables(f)
        for k,spaces in all_subspaces(Q,n):
            if k==0 or k==n:
                assert len(spaces)==1
                assert all(len(code(U,M))==1 for U in spaces)
                continue
            for U in spaces:
                S=dual(U)
                d=rowdist(U,code(U,M))
                assert d==rowdist(S,code(S,M))
                h=min(k,n-k)
                assert max(d)==2*h
                if k>n/2 and set(d)==set(range(0,2*h+1,2)):
                    fws+=1
                count+=1
    print(f"EXACT: all {count} nontrivial binary subspaces in dimensions 2..5; diameter and dual histograms, {fws} high-dimensional r-FWS instances")


if __name__=="__main__":
    witness()
    small_graphs()
