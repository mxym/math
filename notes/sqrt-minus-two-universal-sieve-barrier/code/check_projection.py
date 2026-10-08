#!/usr/bin/env python3
"""Second independent checker: exact local projection criteria, no shift table."""
import json
from math import isqrt
from pathlib import Path

DIR=Path(__file__).resolve().parent
S={tuple(z) for z in json.loads((DIR/'connected_shape.json').read_text())}

def is_prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

if len(S)!=197:raise ValueError('wrong shape size')
counts={'ramified':0,'split':0,'inert':0}
for p in range(2,198):
    if not is_prime(p):continue
    if p==2:
        if len({a%2 for a,b in S})>=2:raise ValueError('ramified local obstruction')
        counts['ramified']+=1
        continue
    roots=[r for r in range(p) if (r*r+2)%p==0]
    if not roots:
        if len({(a%p,b%p) for a,b in S})>=p*p:
            raise ValueError(f'inert local obstruction p={p}')
        counts['inert']+=1
    elif len(roots)==2:
        r=roots[0]
        for sign in (1,-1):
            if len({(a+sign*r*b)%p for a,b in S})>=p:
                raise ValueError(f'split local projection obstruction p={p}')
        counts['split']+=1
    else:raise ValueError('unexpected odd ramification')
if sum(counts.values())!=45:raise ValueError('incomplete local prime classification')
print('INDEPENDENT PROJECTION CERTIFICATE:',counts)
print('EVERY RATIONAL PRIME p<=197 IS LOCALLY ADMISSIBLE')
