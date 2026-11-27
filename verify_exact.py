#!/usr/bin/env python3
from collections import Counter
from itertools import combinations, product

def field_ops(q):
    if q != 4:
        return (lambda a,b:(a+b)%q), (lambda a,b:a*b%q)
    def mul(a,b):
        out=0
        for i in range(2):
            if b>>i&1:
                out ^= a<<i
        if out&4:
            out ^= 7
        return out
    return (lambda a,b:a^b), mul

def evaluate(q,points):
    add,mul=field_ops(q)
    words=[]
    for u in product(range(q),repeat=len(points[0])):
        word=[]
        for P in points:
            value=0
            for a,b in zip(u,P):
                value=add(value,mul(a,b))
            word.append(value)
        words.append(tuple(word))
    assert len(words)==len(set(words))
    return words

def projective(q,k):
    return [tuple([0]*i+[1])+x
            for i in range(k) for x in product(range(q),repeat=k-i-1)]

def statistic(C):
    return Counter(sum(a!=b for a,b in zip(u,v)) for u,v in combinations(C,2))

def check(q,k,s,points):
    C=evaluate(q,points)
    n=len(points)
    assert n==(s+1)*(q+1)+k-2 and len(C)==q**k
    dist=statistic(C)
    assert min(dist)==(s+1)*q
    assert set(dist) <= {min(dist),*range(n-k+3,n+1)}
    for i in range(n):
        counts=Counter(u[i] for u in C)
        assert set(counts)==set(range(q)) and set(counts.values())=={q**(k-1)}
        for j in range(i):
            counts=Counter((u[i],u[j]) for u in C)
            assert len(counts)==q*q and set(counts.values())=={q**(k-2)}
    print(f"q={q} k={k} s={s}: n={n}, pairs={dict(sorted(dist.items()))}")

check(3,2,0,projective(3,2))
check(2,3,1,projective(2,3))
check(3,3,2,projective(3,3))
check(5,3,4,projective(5,3))
check(5,3,3,[(1,x,y) for x,y in product(range(5),repeat=2)])
_,mul=field_ops(4)
check(4,3,0,[(1,x,mul(x,x)) for x in range(4)]+[(0,0,1),(0,1,0)])
check(2,4,1,[(1,*xyz) for xyz in product(range(2),repeat=3)])

# Distinct q=5,h=3 and q=4,h=6 numerical exclusions.
for q,k,h,n in ((5,3,3,13),(4,4,6,22)):
    r=1+n*(q-1)
    assert q**k>r and n%h
    print(f"obstruction q={q} k={k}: rank ceiling {r} < {q**k}; ({n} mod {h})={n%h}")
