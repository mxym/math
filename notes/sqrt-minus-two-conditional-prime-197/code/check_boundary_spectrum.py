#!/usr/bin/env python3
"""Independent exact checker for local composite-boundary blockers for all 197
connected prefixes of the known universally norm-admissible shape.

Output certifies ONLY modular nondivisibility and inert-prime boundary
blocking inputs. It does NOT assert Schinzel H or actual prime values.
"""
import json
from hashlib import sha256
from math import isqrt
from pathlib import Path

HERE=Path(__file__).resolve().parent
S_PATH=HERE.parents[1]/'sqrt-minus-two-universal-sieve-barrier'/'code'/'connected_shape.json'
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))


def require(ok,msg):
    if not ok:raise ValueError(msg)


def prime(n):
    return type(n) is int and n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def check():
    require(sha256(S_PATH.read_bytes()).hexdigest()==
            'b8036dcfa082e1329126041d8c7992139da6121e4ebf71599458619e7af93df0',
            'untrusted parent shape bytes')
    S={tuple(z) for z in json.loads(S_PATH.read_text())}
    require(len(S)==197,'wrong parent shape cardinality')
    inert=json.loads((HERE/'inert_boundary_primes.json').read_text())
    require(type(inert) is list and len(inert)==1186,'incomplete inert prime blockers')
    require(inert==sorted(set(inert)),'inert prime order/repetitions invalid')
    require(inert[0]==397 and inert[-1]==46237,'unexpected inert blockers')
    for p in inert:
        require(prime(p) and p>394 and p%8==5 and pow(-2,(p-1)//2,p)==p-1,
                f'nonprime or noninert boundary blocker p={p}')
    print('INERT BLOCKERS: 1186 exact rational primes, all >394 and inert in Q(sqrt(-2))')

    # Select a deterministic connected spanning-tree traversal of the 197
    # points, ensuring every prefix is itself connected under the 14 steps.
    seq=[min(S)]
    seen={seq[0]}
    for a,b in seq:
        for da,db in F:
            z=(a+da,b+db)
            if z in S and z not in seen:
                seen.add(z)
                seq.append(z)
    require(len(seq)==197,'not a spanning traversal of the parent graph')

    largest_boundary=0
    evaluated=0
    for k in range(1,198):
        shape=set(seq[:k])
        boundary=sorted({(a+da,b+db) for a,b in shape for da,db in F}-shape)
        largest_boundary=max(largest_boundary,len(boundary))
        require(len(boundary)<=len(inert),'more boundary points than certified blockers')
        for j,w in enumerate(boundary):
            p=inert[j]
            wx,wy=w
            for x,y in shape:
                # q | N((x,y)-(wx,wy)) would obstruct the CRT class
                # designed to force this boundary point into (q).
                require(((x-wx)**2+2*(y-wy)**2)%p!=0,
                        f'boundary prime {p} obstructs inner point at prefix {k}')
                evaluated+=1
    require(largest_boundary==1186,'claimed maximum boundary size changed')
    print('EXACT PREFIXES: all 197 connected prefixes, maximal exterior boundary 1186')
    print('LOCAL BOUNDARY CHECKS:',evaluated,'integer norm nonvanishing predicates verified')
    print('BOUNDARY BLOCKING INPUTS VERIFIED; PRIME COMPONENT SPECTRUM IS CONDITIONAL ON SCHINZEL H')


if __name__=='__main__':
    check()
