#!/usr/bin/env python3
"""Independent exact finite checker for a connected universally norm-admissible
197-point shape in the Z[sqrt(-2)] coefficient lattice.

No solver, generator import, probability, floating point or network.
The paper proves why finitely many modular tests suffice for *all* primes.
"""
import json
from math import isqrt
from pathlib import Path

DIR=Path(__file__).resolve().parent
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))


def demand(test,msg):
    if not test:raise ValueError(msg)


def norm(p):
    a,b=p
    return a*a+2*b*b


def is_prime(n):
    return type(n) is int and n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def verify(shape,shifts):
    demand(type(shape) is list and len(shape)==197,'wrong shape cardinality')
    S={tuple(p) for p in shape}
    demand(len(S)==197 and all(len(p)==2 and all(type(z) is int for z in p) for p in S),
           'repeated or noninteger shape points')
    demand(min(p[0] for p in S)==369 and max(p[0] for p in S)==413,
           'unexpected first-coordinate extent')
    demand(min(p[1] for p in S)==-34 and max(p[1] for p in S)==34,
           'unexpected second-coordinate extent')
    demand(all(0<norm(f)<=6 for f in F) and len(set(F))==14,
           'step set incorrect')
    unseen=set(S)
    start=unseen.pop()
    queue=[start]
    for a,b in queue:
        for da,db in F:
            neighbor=a+da,b+db
            if neighbor in unseen:
                unseen.remove(neighbor)
                queue.append(neighbor)
    demand(not unseen and len(queue)==197,'shape not connected with 14 allowed steps')
    print('SHAPE: 197 distinct connected lattice points; bounds a=369..413, b=-34..34')

    expected={str(p) for p in range(2,198) if is_prime(p)}
    demand(type(shifts) is dict and set(shifts)==expected,
           'incomplete or polluted prime-indexed local shifts')
    demand(len(shifts)==45,'unexpected count of rational prime tests')
    for key,values in shifts.items():
        p=int(key)
        demand(len(values)==2 and all(type(u) is int and 0<=u<p for u in values),
               'noncanonical local translation vector')
        u,v=values
        for a,b in S:
            demand(((a+u)*(a+u)+2*(b+v)*(b+v))%p!=0,
                   f'forbidden norm-zero value modulo p={p}')
    print('LOCAL: complete literal admissible shifts for all 45 primes p<=197')

    # Sound finite sanity tests of the underlying split/inert dichotomy.
    # The proof for p>197 follows from residue projections, not this loop.
    for p in (3,5,7,11,17,19,41,43,59,67,73,83,89,97,107,113,131,197):
        roots=[z for z in range(p) if (z*z+2)%p==0]
        demand(len(roots) in (0,2),'unexpected ramification at odd p')
        if roots:
            r=roots[0]
            for a in range(p):
                for b in range(p):
                    demand((norm((a,b))%p==0)==((a+r*b)%p==0 or (a-r*b)%p==0),
                           'invalid modular split identity')
    print('ALGEBRA: exact split/inert modular norm identities checked on selected primes')
    print('ALL FINITE PROOF WITNESSES VERIFIED')


if __name__=='__main__':
    shape=json.loads((DIR/'connected_shape.json').read_text())
    shifts=json.loads((DIR/'local_shifts.json').read_text())
    verify(shape,shifts)
