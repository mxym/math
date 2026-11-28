#!/usr/bin/env python3
"""Exact finite arithmetic for exact-energy-shell-residue-cutoff.md."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt
from functools import reduce


FORMS = (
    ((F(1),),),
    ((F(1),F(0)), (F(0),F(1))),
    ((F(1),F(1,2)), (F(1,2),F(1))),
    ((F(1),F(1)), (F(1),F(3))),
    ((F(2),F(1,2)), (F(1,2),F(2))),
)


def add(x,y,k):
    return tuple(a+k*b for a,b in zip(x,y))


def form(G,x,y):
    return sum(x[i]*G[i][j]*y[j] for i,j in product(range(len(G)),repeat=2))


def inverse(G):
    if len(G)==1:
        return ((1/G[0][0],),)
    a,b = G[0]
    _,d = G[1]
    det = a*d-b*b
    return ((d/det,-b/det),(-b/det,a/det))


def ilim(z):
    return isqrt(z.numerator//z.denominator)


def gcd_and_shells():
    gcd_rows = shell_rows = modular_rows = 0
    for G in FORMS:
        d = len(G)
        chosen = tuple(product(range(-2,3),repeat=d))
        def energy(x):
            q0 = form(G,x,x)
            assert q0.denominator==1
            return int(q0)
        assert reduce(gcd,(energy(x) for x in chosen),0)==1
        b = reduce(gcd,(int(2*form(G,x,y)) for x,y in product(chosen,repeat=2)),0)
        assert b in (1,2)
        inv = inverse(G)
        bounds = [ilim(inv[i][i]*7) for i in range(d)]
        points = [(x,energy(x)) for x in product(*(range(-k,k+1) for k in bounds))
                  if energy(x)<=7]
        for q in range(2,7):
            c = q*gcd(q,b)
            vals = (
                energy(add(x,y,q))-energy(x) for x,y in product(chosen,repeat=2)
            )
            assert reduce(gcd,vals,0)==c
            gcd_rows+=1
            classes = tuple(product(range(q),repeat=d))
            residues = [energy(r)%c for r in classes]
            for k in range(1,c):
                assert any(k*x%c for x in residues)
                modular_rows+=1
            for tup in product(points,repeat=3):
                E = sum(a for _,a in tup)
                if E>7:
                    continue
                projected = [tuple(z%q for z in x) for x,_ in tup]
                assert sum(energy(x) for x in projected)%c == E%c
                shell_rows+=1
    return gcd_rows,modular_rows,shell_rows


def shortest_collision():
    n = 0
    for G in FORMS:
        d=len(G)
        H = inverse(G)
        sample = H[0][0]
        bounds = [ilim(G[i][i]*sample) for i in range(d)]
        candidates = tuple(x for x in product(*(range(-x,x+1) for x in bounds))
                           if any(x))
        least = min(form(H,x,x) for x in candidates)
        short = [x for x in candidates if form(H,x,x)==least]
        for q in range(2,9):
            groups = Counter(tuple(a%q for a in x) for x in short)
            assert tuple(0 for _ in range(d)) not in groups
            assert sum(k*k for k in groups.values()) == len(short)*(2 if q==2 else 1)
            n += 1
    return n


if __name__=="__main__":
    g,m,s=gcd_and_shells()
    a=shortest_collision()
    print(f"PASS: {g} exact common-span gcds, {m} nontrivial congruence characters")
    print(f"PASS: {s} shell residues and {a} exact shortest-character collision checks")
