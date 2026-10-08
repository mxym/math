#!/usr/bin/env python3
"""Independent six-level exact-integer checker for the optimal 197-point sieve.

The 197 lower obstruction is in the separate published paper. This program
independently proves a 197 upper bound for one explicit finite principal-ideal
sieve by exhaustively refining the SHA256-pinned period-1122 components under
moduli 19, 5, 41, 43, 59, 67. All levels use literal integer norms and exact
connected-component traversal, not the C++ exploratory algorithm.
"""
import argparse
from collections import deque
import gzip
import hashlib
import json
from pathlib import Path
from math import gcd,isqrt,prod

HERE=Path(__file__).resolve().parent
PARENT=HERE.parents[1]/'sqrt-minus-two-sqrt6-period'/'code'
RAW_PARENT=PARENT/'positive_q1122.json.gz'
RAW_EXCEPT=PARENT/'exceptional_closure.json'
PARENT_SHA='86f44f88613a6e7f3f4808c6611ac76bd689b1d876eea27f10cf29eb953df314'
EXCEPT_SHA='b4b5c81b3a566a038c859e005146f6076326f5eee4c76afd0406a347989e41e6'
Q=1122
TARGET=197
MODULI=(19,5,41,43,59,67)
STEPS=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
       (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))
EXPECTED_SHIFTS=(74366,3500,20172,66564,69620,53868)
EXPECTED_LARGE=(140,12,36,20,12,0)
EXPECTED_MAX=(298,241,217,205,201,197)


def demand(test,msg):
    if not test:raise ValueError(msg)


def norm(z):
    a,b=z
    return a*a+2*b*b


def divides(g,z):
    a,b=g;c,d=z;n=norm(g)
    return n>0 and (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0


def verify_moduli():
    demand(len(set(MODULI))==len(MODULI) and
           all(p>=2 and all(p%d for d in range(2,isqrt(p)+1))
               and gcd(p,Q)==1 for p in MODULI),
           'refinement moduli must be distinct rational primes coprime to Q')
    demand(Q*prod(MODULI)==742840526010,
           'full scalar period of the refined ideal sieve is incorrect')


def pinned_inputs():
    demand(RAW_PARENT.exists() and RAW_EXCEPT.exists(),
           'a required immutable parent source is not in the repository')
    demand(hashlib.sha256(RAW_PARENT.read_bytes()).hexdigest()==PARENT_SHA,
           'parent full positive partition was modified')
    demand(hashlib.sha256(RAW_EXCEPT.read_bytes()).hexdigest()==EXCEPT_SHA,
           'parent exceptional closure was modified')
    with gzip.open(RAW_PARENT,'rt',encoding='utf-8') as f:data=json.load(f)
    demand(set(data)=={'q','components'} and data['q']==Q,
           'inconsistent parent certificate header')
    components=data['components']
    demand(len(components)==6688 and sum(map(len,components))==204800,
           'incomplete parent positive partition')
    return components,json.loads(RAW_EXCEPT.read_text())


def verify_extra_prime_factors(closure):
    C={tuple(z) for z in closure}
    demand(len(closure)==len(C)==92,'wrong inherited exceptional set')
    g={5:((5,0),),19:((1,3),(1,-3)),41:((3,4),(3,-4)),
       43:((5,3),(5,-3)),59:((3,5),(3,-5)),
       67:((7,3),(7,-3))}
    demand(tuple(g)==(5,19,41,43,59,67),'prime list is incomplete')
    exceptional=set()
    for p,gs in g.items():
        if p==5:
            demand(len(gs)==1 and norm(gs[0])==25,
                   'wrong inert prime over five')
        else:
            demand(len(gs)==2 and all(norm(z)==p for z in gs),
                   f'incorrect prime-norm factors above {p}')
        for gen in gs:
            demand(divides(gen,(p,0)),f'generator does not divide {p}')
            exceptional.add(gen)
            exceptional.add((-gen[0],-gen[1]))
        # Independently enumerate the entire residue square mod p to
        # verify the two split ideals or the inert singleton ideal.
        for a in range(p):
            for b in range(p):
                test=(norm((a,b))%p==0)
                ideal=any(divides(z,(a,b)) for z in gs)
                demand(test==ideal, f'modular factorization incorrect at p={p}')
    demand(len(exceptional)==22 and exceptional<=C,
           'a new prime exception lies outside the old closed component')
    print('EXCEPTIONS: all 22 added prime associates over 5,19,41,43,59,67 lie in the certified 90-prime component')


def adjacency(points):
    lookup={z:i for i,z in enumerate(points)}
    demand(len(lookup)==len(points),'duplicate parent component point')
    return [tuple(lookup.get((x+da,y+db),-1) for da,db in STEPS if
                  (x+da,y+db) in lookup) for x,y in points]


def components_of(candidate,edges):
    """Induced connected components by independent set/BFS implementation."""
    remaining=set(candidate)
    while remaining:
        start=remaining.pop()
        comp=[start]
        for z in comp:
            for v in edges[z]:
                if v in remaining:
                    remaining.remove(v)
                    comp.append(v)
        yield comp


def scan_one_parent(index,raw,stats):
    points=[tuple(v) for v in raw]
    edges=adjacency(points)
    all_indices=tuple(range(len(points)))
    scratch=[]

    def stage(nodes,layer,shift_x,shift_y,multiplier):
        p=MODULI[layer]
        # The nested q-periodic translates are indexed by the mixed-radix
        # vector u0 + p0*u1 + ... . Every such tuple is enumerated.
        xmod=[(points[i][0]+Q*shift_x)%p for i in nodes]
        ymod=[(points[i][1]+Q*shift_y)%p for i in nodes]
        delta=(Q*multiplier)%p
        for ux in range(p):
            xs=[(z+delta*ux)%p for z in xmod]
            x2=[z*z for z in xs]
            for uy in range(p):
                stats['shift'][layer]+=1
                # Actual filter N(point + Q * translate) != 0 mod p.
                ys=[(z+delta*uy)%p for z in ymod]
                filtered=(nodes[k] for k,y in enumerate(ys)
                          if (x2[k]+2*y*y)%p)
                for sub in components_of(filtered,edges):
                    length=len(sub)
                    if length>stats['peak'][layer]:
                        stats['peak'][layer]=length
                        if layer==len(MODULI)-1:
                            stats['witness']=(index,tuple(scratch)+((ux,uy),))
                    if length<=TARGET:continue
                    stats['large'][layer]+=1
                    demand(layer<len(MODULI)-1,
                           f'counterexample final connected sieve piece length {length}')
                    scratch.append((ux,uy))
                    stage(sub,layer+1,shift_x+multiplier*ux,
                          shift_y+multiplier*uy,multiplier*p)
                    scratch.pop()

    stage(all_indices,0,0,0,1)


def verify_upper(groups,part=0,parts=1):
    demand(type(part) is int and type(parts) is int and
           0<=part<parts<=20,'invalid deterministic checker partition')
    all_large=[i for i,C in enumerate(groups) if len(C)>TARGET]
    demand(len(all_large)==206,'wrong number of relevant parent groups')
    selected=[i for i in all_large if i%parts==part]
    stats={'shift':[0]*len(MODULI),'large':[0]*len(MODULI),
           'peak':[0]*len(MODULI),'witness':None}
    for i in selected:
        scan_one_parent(i,groups[i],stats)
    print(f'PARTITION: {part+1}/{parts}; examined {len(selected)} parent components >197')
    print('SHIFT CONFIGURATIONS:',stats['shift'])
    print('LARGE COMPONENTS:',stats['large'])
    print('LAYER MAXIMA:',stats['peak'],'attainment',stats['witness'])
    if parts==1:
        demand(tuple(stats['shift'])==EXPECTED_SHIFTS,
               'incomplete six-stage CRT shift coverage')
        demand(tuple(stats['large'])==EXPECTED_LARGE,
               'unexpected count of intermediate oversized pieces')
        demand(tuple(stats['peak'])==EXPECTED_MAX,
               'unexpected exact integer sieve maxima')
        print('SHARP SIEVE: complete infinite allowed lattice has no component larger than 197')
        print('ALL EXACT CERTIFICATES VERIFIED')
    return stats


if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('--part',type=int,default=0)
    cli.add_argument('--parts',type=int,default=1)
    args=cli.parse_args()
    verify_moduli()
    groups,closure=pinned_inputs()
    verify_extra_prime_factors(closure)
    verify_upper(groups,part=args.part,parts=args.parts)
