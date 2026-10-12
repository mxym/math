#!/usr/bin/env python3
"""Exact join-of-simplex-products certificate producer through D=56."""
from fractions import Fraction as F
from math import comb
from functools import lru_cache
from pathlib import Path
import json

@lru_cache(maxsize=None)
def block(p,q):
    n=p+q
    return F(n)/(F(p,p+1)+F(q,q+1)),F(comb(n,p)*p**p*q**q*(n+2*p*q),n**(n+1))


def main():
    levels=[[(F(0),F(1),['empty'])]]
    summary=[]
    for D in range(1,57):
        candidates={}
        def keep(h,q,op):
            old=candidates.get(h)
            if old is None or q>old[0]:candidates[h]=(q,op)
        for i,(h,q,_) in enumerate(levels[D-1]):
            keep(h+1,q,['point',D-1,i])
        for T in range(3,D+1):
            for p in range(1,(T-1)//2+1):
                q=T-1-p
                hb,qb=block(p,q)
                for i,(h,v,_) in enumerate(levels[D-T]):
                    keep(h+hb,v*qb,['block',D-T,i,p,q])
        frontier=[];bestq=F(0)
        for h,(q,op) in sorted(candidates.items(),reverse=True):
            if q>bestq:
                frontier.append((h,q,op));bestq=q
        levels.append(frontier)
        winner=max(range(len(frontier)),key=lambda i:frontier[i][0]*frontier[i][1])
        h,q,_=frontier[winner];ratio=h*q/F(D)
        summary.append({'D':D,'frontier_size':len(frontier),'winning_index':winner,
                        'sharp_ratio':str(ratio)})
        if D%8==0 or D==56:print(D,len(frontier),ratio,flush=True)
    out=Path('notes/projection-first-nesting-d55/certificates/two_layer56.json')
    out.write_text(json.dumps({'max_D':56,
            'frontiers':[[{'H':str(h),'Q':str(q),'op':op} for h,q,op in row] for row in levels],
            'summary':summary},separators=(',',':'))+'\n')
    print('WROTE',out,'STATES',sum(len(z) for z in levels))


if __name__=='__main__':main()
