#!/usr/bin/env python3
"""Produce the exact d49..55 extension from the independently pinned 48D base.

All arithmetic and choice of dominating states uses integer/Fraction only.
The checker is an independent source file and must be run separately.
"""
import hashlib
import json
import sys
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
BASE=ROOT.parent/'exact-product-join-finite-optima'/'certificates'/'frontiers48.json'
DEFAULT=ROOT/'certificates'/'all_tree49to55.json'

@lru_cache(maxsize=None)
def g(d):return F(d**d,factorial(d))


def build(filename=DEFAULT):
    base=json.loads(BASE.read_text())
    if base['max_dimension']!=48:raise ValueError('expected exact 48D parent')
    levels=[[(F(st['H']),F(st['Q']),st['op']) for st in layer]
            for layer in base['states']]
    summaries=[]
    extended=[]
    for d in range(49,56):
        candidates={}
        def add(h,q,op):
            previous=candidates.get(h)
            if previous is None or previous[0]<q:
                candidates[h]=(q,op)
        for r in range(d):
            s=d-1-r
            if r>s:break
            for i,(ha,qa,_) in enumerate(levels[r]):
                for j,(hb,qb,_) in enumerate(levels[s]):
                    add(ha+hb,qa*qb,['join',r,i,s,j])
        for r in range(1,d):
            s=d-r
            if r>s:break
            C=g(r)*g(s)/g(d)
            for i,(ha,qa,_) in enumerate(levels[r]):
                for j,(hb,qb,_) in enumerate(levels[s]):
                    add(F(d)*ha*hb/(r*hb+s*ha),
                        qa*qb*C*F(s*ha+r*hb,d),
                        ['product',r,i,s,j])
        front=[];bestQ=F(0)
        for h,(q,op) in sorted(candidates.items(),reverse=True):
            if q>bestQ:
                front.append((h,q,op));bestQ=q
        levels.append(front)
        extended.append([{'H':str(h),'Q':str(q),'op':op} for h,q,op in front])
        best_index=max(range(len(front)),key=lambda i:front[i][0]*front[i][1])
        h,q,_=front[best_index]
        summaries.append({'dimension':d,'frontier_size':len(front),'best_index':best_index,
                          'exact_ratio':str(h*q/F(d+1))})
        print(f'dimension={d}, exact frontier size={len(front)}, exact optimum={h*q/F(d+1)}',flush=True)
    cert={'base_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),
          'first_dimension':49,'last_dimension':55,
          'frontiers':extended,'summary':summaries}
    p=Path(filename)
    p.write_text(json.dumps(cert,separators=(',',':'))+'\n')
    print('WROTE',p,'new_states=',sum(len(r) for r in extended))

if __name__=='__main__':build(sys.argv[1] if len(sys.argv)>1 else DEFAULT)
