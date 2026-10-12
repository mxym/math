#!/usr/bin/env python3
"""Untrusted producer for an exact spectrum-blocking finite prime list.

Every prime in this list is inert in Z[sqrt(-2)] and greater than 394.
The independent checker validates the list and ALL 197 connected prefixes.
"""
import json
from math import isqrt
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'sqrt-minus-two-universal-sieve-barrier'/'code'
S={tuple(p) for p in json.loads((BASE/'connected_shape.json').read_text())}
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))

def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

order=[min(S)];seen={order[0]}
for a,b in order:
    for da,db in F:
        z=a+da,b+db
        if z in S and z not in seen:
            seen.add(z);order.append(z)
if len(order)!=len(S):raise ValueError('pattern not connected')

boundary_sizes=[]
for k in range(1,len(S)+1):
    T=set(order[:k])
    boundary_sizes.append(len({(a+da,b+db) for a,b in T for da,db in F}-T))
needed=max(boundary_sizes)
primes=[]
n=395
while len(primes)<needed:
    if n%8==5 and prime(n):primes.append(n)
    n+=1
HERE.joinpath('inert_boundary_primes.json').write_text(
    json.dumps(primes,separators=(',',':'))+'\n')
print('Connected prefixes',len(S),'largest external boundary',needed,
      'first inert prime',primes[0],'last inert prime',primes[-1])
