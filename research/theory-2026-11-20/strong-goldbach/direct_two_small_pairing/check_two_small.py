#!/usr/bin/env python3
"""Replay the exact physical divisor identities with rational log profiles."""
from math import prod
from random import Random
from fractions import Fraction


def must(c, what):
    if not c:
        raise ArithmeticError(what)


def subs(a):
    n=a
    while True:
        yield n
        if not n:
            return
        n=(n-1)&a


def signs(es):
    n=len(es)
    p,q=es[:2]
    L=sum(es)
    full=(1<<n)-1
    macro=full^3
    logs=[sum(es[i] for i in range(n) if m>>i&1) for m in range(1<<n)]
    if any(2*K==L for K in logs):  # true squarefree y cannot have this tie
        return None
    raw=0
    for a in subs(full):
        if 2*logs[a]>L:
            raw+=(-1)**a.bit_count()*logs[full^a]
    for c in range(4):
        for a in subs(full^c):
            if 2*logs[a]>L:
                raw+=(-2)**c.bit_count()*logs[full^(c|a)]
    reconstructed=0
    for d in subs(macro):
        v=macro^d
        eta=(-1)**d.bit_count()
        t=2*logs[d]
        exact=sum((-1)**u.bit_count()*((eta+1)*logs[v]+(eta-1)*logs[3^u])
                  for u in range(4) if t+2*logs[u]>L)
        if L-2*p<t<L:
            table=(-2*logs[v] if eta==1 else 2*(p+q))
        elif L-2*q<t<L-2*p:
            table=(0 if eta==1 else 2*p)
        elif L-2*(p+q)<t<L-2*q:
            table=(2*logs[v] if eta==1 else 0)
        else:
            table=0
        must(table==exact,("literal table",es,d,table,exact))
        reconstructed+=table
        if L-2*p<t<L:
            opposite=(-1)**v.bit_count()
            if macro.bit_count()%2:
                pair=table+(2*logs[d] if opposite==1 else 0)
                expect=L-2*logs[v]-eta*L
                must(pair==expect and L-2*logs[v]>2*q,("odd pair",es,d,pair,expect))
                must(Fraction(eta-opposite,2)==eta,("antisymmetric sign",es,d))
            else:
                must(eta==opposite,("even sign",es,d))
    must(raw==reconstructed,("complete exact score",es,raw,reconstructed))
    if macro.bit_count()%2==0:
        must(raw>=0,("even macro lower",es,raw))
    return raw


def run():
    rng=Random(273766)
    counts=[0,0]
    for rank in range(2,12): # macro factors, each larger than p and q
        for _ in range(220):
            a=rng.randrange(1,50)
            b=rng.randrange(a+1,80)
            es=(a,b)+tuple(rng.randrange(100,10000) for _ in range(rank))
            r=signs(es)
            if r is not None:
                counts[rank%2]+=1
    # At least one genuine angular pattern carries an unpriced odd negative.
    r=signs((10,15,2480,2518,4978))
    must(r is not None and r<0,("odd negative witness",r))
    must(sum(counts)>1800,"test coverage")
    print("even/odd exact profiles:",counts,"odd negative witness:",r)


if __name__=="__main__":
    run()
