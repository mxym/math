#!/usr/bin/env python3
"""Nontrusted deterministic producer for the local-shift witness table.

The independent checker validates the literal output from scratch.
"""
import json
from math import isqrt
from pathlib import Path

DIR=Path(__file__).resolve().parent
S=json.loads((DIR/'connected_shape.json').read_text())

def is_prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

out={}
for p in range(2,len(S)+1):
    if not is_prime(p):continue
    found=False
    for sx in range(p):
        for sy in range(p):
            if all(((a+sx)**2+2*(b+sy)**2)%p for a,b in S):
                out[str(p)]=[sx,sy]
                found=True
                break
        if found:break
    if not found:raise RuntimeError(f'candidate shape is not admissible modulo {p}')
path=DIR/'local_shifts.json'
path.write_text(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n')
print('complete local certificates',len(out),'for shape size',len(S))
