#!/usr/bin/env python3
"""Independent exact producer of all depth-two finite split maximum witnesses.

The source of the completeness/upper proof is paper.md. This generator is
NOT imported by the checker. Every arithmetic comparison is Fraction only.
"""
import json
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
PRIOR=ROOT.parent/'projection-first-nesting-d55'/'certificates'/'two_layer56.json'
CONT=ROOT.parent/'projection-persistent-nesting-gap'/'certificates'/'extension57to85.json'
OUT=ROOT/'certificates'/'finite_splits.tsv'

@lru_cache(maxsize=None)
def g(n):return F(n**n,factorial(n))


def produce():
    p=json.loads(PRIOR.read_text())['frontiers']
    p+=json.loads(CONT.read_text())['frontiers']
    states={d:[(F(v['H']),F(v['Q'])) for v in p[d+1]] for d in range(1,80)}
    lines=['r\ts\twinner_i\twinner_j\tbest_product_Q']
    count=0
    for r in range(1,80):
        for s in range(r,80):
            if r>11 and r+s>62:continue
            best=F(0);winner=(-1,-1)
            for i,(h,u) in enumerate(states[r]):
                for j,(k,v) in enumerate(states[s]):
                    val=(u*v)*(s*h+r*k)
                    if val>best:
                        best=val;winner=(i,j)
                    count+=1
            n=r+s
            q=best*g(r)*g(s)/(F(n)*g(n))
            lines.append(f'{r}\t{s}\t{winner[0]}\t{winner[1]}\t{q}')
    OUT.write_text('\n'.join(lines)+'\n')
    print('WROTE',OUT,'dimension splits',len(lines)-1,'exact input pairs',count)

if __name__=='__main__':produce()
