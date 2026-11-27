"""Exact full dealer and projected supports using dense GF(2) matrix operations."""
from collections import Counter
from functools import reduce
from fractions import Fraction
from itertools import combinations, product
from operator import xor

def model(n, ):
    N=n-1
    L=[[int(i>=j) for j in range(N)] for i in range(N)]
    L[0][2]^=1
    L[2][0]^=1
    def f(a,b):
        return (sum(a[i]*L[i][j]*b[j] for i,j in product(range(N),repeat=2))+a[0])%2
    def code(a,b):
        return tuple(2*x+y for x,y in zip(a,b))+(2*(sum(a)%2)+sum(b)%2,)
    def share(secret,coins_a,coins_b):
        a=(0,)+coins_a
        b=coins_b
        if f(a,b)!=secret:
            a=tuple(x^(i<3) for i,x in enumerate(a))
        return code(a,b)
    def recover(Y):
        if None in Y:
            pos=Y.index(None)
            Y=Y[:pos]+(reduce(xor,(t for t in Y if t is not None),0),)+Y[pos+1:]
        a,b=tuple(t//2 for t in Y[:-1]),tuple(t%2 for t in Y[:-1])
        return f(a,b)
    return share,recover

def props(n):
    share,recover=model(n)
    N=n-1
    words=[]
    for s in (0,1):
        C={share(s,coin_a,coin_b) for coin_a in product((0,1),repeat=N-1)
             for coin_b in product((0,1),repeat=N)}
        assert len(C)==2**(2*N-1)
        assert all(reduce(xor,w,0)==0 and recover(w)==s for w in C)
        words.append(C)
    assert words[0].isdisjoint(words[1])
    assert len(words[0])+len(words[1])==4**N
    for s,ws in enumerate(words):
        for w in ws:
            for i in range(n):
                assert recover(w[:i]+(None,)+w[i+1:])==s
    full=set(range(n))
    counts=0
    ratio=set()
    for i,j in combinations(range(n),2):
        vis=sorted(full-{i,j})
        D=[Counter(tuple(w[k] for k in vis) for w in T) for T in words]
        assert D[0].keys()==D[1].keys() and len(D[0])==4**(n-2)
        for z,v in D[0].items():
            assert {v,D[1][z]}=={1,3}
            ratio.add(Fraction(v,D[1][z]))
        counts+=len(D[0])
    assert ratio=={Fraction(1,3),Fraction(3,1)}
    return len(words[0]),counts

def small():
    for n in [2,3]:
        C=[[(s,)*n] if n==2 else [tuple(r^(s*k) for k in range(n)) for r in range(4)]
           for s in (0,1)]
        for J in combinations(range(n),n-1):
            D=[Counter(tuple(w[i] for i in J) for w in T) for T in C]
            assert D[0].keys().isdisjoint(D[1].keys())
        for J in combinations(range(n),n-2):
            D=[Counter(tuple(w[i] for i in J) for w in T) for T in C]
            assert D[0]==D[1]
    print("n=2,3 boundary exactly perfectly private and always correct: PASS")

if __name__=='__main__':
    small()
    for n in range(4,9):
        print("exact full dealer n=%d: %d words per secret, %d maximal unauthorized views, ratios {1/3,3}" %
              (n,*props(n)))
