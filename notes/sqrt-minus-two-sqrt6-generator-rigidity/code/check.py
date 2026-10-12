#!/usr/bin/env python3
"""Exact independent checker for all eight omitted-prime voltage witnesses.

Does not import or call the producer; all validation is integer arithmetic.
"""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
Q=1122
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))
P=((0,1),(1,1),(1,-1),(3,1),(3,-1),(3,2),(3,-2))
RAMIFIED_SQUARE=(-2,0)


def demand(valid,reason):
    if not valid:raise ValueError(reason)


def norm(z):
    a,b=z
    return a*a+2*b*b


def divides(g,z):
    a,b=g;c,d=z;n=norm(g)
    return n>0 and (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0


def validate_walk(case,missing,ramified=False):
    demand(type(missing) is int and 0<=missing<7,'missing prime index invalid')
    demand(set(case)=={'missing','start','steps'},'unexpected certificate fields')
    demand(case['missing']==missing,'index mismatch')
    gens=[g for j,g in enumerate(P) if j!=missing]
    if ramified:gens.append(RAMIFIED_SQUARE)
    for gen in gens:
        demand(divides(gen,(Q,0)),'not a 1122-periodic principal ideal')
    start=tuple(case['start'])
    demand(len(start)==2 and all(type(t) is int and 0<=t<Q for t in start),
           'noncanonical start')
    def free(z):return not any(divides(g,z) for g in gens)
    demand(free(start),'start lies in deleted ideal')
    steps=case['steps']
    demand(type(steps) is list and 0<len(steps)<2000,'bad step count')
    current=start
    for move in steps:
        demand(type(move) is int and 0<=move<len(F),'step index invalid')
        dx,dy=F[move]
        current=current[0]+dx,current[1]+dy
        demand(free(current),'intermediate vertex deleted')
    demand(current!=start and all((current[j]-start[j])%Q==0 for j in (0,1)),
           'no nonzero period voltage')
    return len(steps)



def multiply(p,q):
    a,b=p;c,d=q
    return a*c-2*b*d,a*d+b*c


def check_factorization():
    demand([norm(g) for g in P]==[2,3,3,11,11,17,17],
           'incorrect prime norm factors')
    product=(1,0)
    for g in (P[0],)+P:
        product=multiply(product,g)
    demand(product in ((Q,0),(-Q,0)),'incomplete factorization of 1122')
    for g in P:
        n=norm(g)
        demand(divides(g,(n,0)),'prime generator not dividing its rational norm')
        demand(all(not divides(g,(j,0)) for j in range(1,n)),
               'least scalar period not prime norm')
    demand(divides(RAMIFIED_SQUARE,(Q,0)),'ramified square not periodic')


def check(data):
    check_factorization()
    demand(set(data)=={'prime_omissions','ramified_square'},'incorrect sections')
    require=data['prime_omissions']
    demand(type(require) is list and len(require)==7,'seven omissions not supplied')
    seen={};lengths=[]
    for item in require:
        k=item['missing']
        demand(type(k) is int and k not in seen,'repeated prime index')
        seen[k]=True
        lengths.append((k,validate_walk(item,k)))
    demand(set(seen)==set(range(7)),'not all seven prime ideals excluded')
    sq=data['ramified_square']
    demand(sq['missing']==0,'square replacement must omit ramified prime t')
    sq_length=validate_walk(sq,0,ramified=True)
    demand(sorted(lengths)==[(0,624),(1,567),(2,567),(3,669),
                            (4,669),(5,759),(6,759)],
           'expected seven exact negative path lengths differ')
    demand(sq_length==854,'unexpected ramified-square witness length')
    for g,expected in [((1,0),False),((0,0),True),((0,1),True),
                       ((1,1),True),((3,1),True),((3,2),True)]:
        # This is just a small independent check of the exact divisor predicate,
        # not a primality algorithm.
        contained=any(divides(p,g) for p in P)
        demand(contained==expected,'small ideal-incidence regression')
    print('PRIME OMISSIONS:', sorted(lengths))
    print('RAMIFIED SQUARE: exact nonzero 1122-voltage walk of',sq_length,'steps')
    print('ALL EIGHT EXACT CERTIFICATES VERIFIED')


if __name__=='__main__':
    check(json.loads((ROOT/'obstructions.json').read_text()))
