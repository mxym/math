#!/usr/bin/env python3
"""Exact rational certificate producer for persistent projection nesting gap.

Extends the pre-certified point/block join Pareto frontiers E_D from D=56
through D=85 and writes explicit finite witnesses. This producer is NOT
trusted by the independent verification program check.py.
"""
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent.parent
BASE=HERE.parent/'projection-first-nesting-d55'/'certificates'/'two_layer56.json'
OUT=HERE/'certificates'/'extension57to85.json'
PIN='101ffdf287f984965c941b1f98f93de89ae4a3bd0d4e796f02558a8039cb3d9f'

@lru_cache(maxsize=None)
def g(n):return F(n**n, factorial(n))

@lru_cache(maxsize=None)
def atom(p,q):
    n=p+q
    return F(n)/(F(p,p+1)+F(q,q+1)),F(comb(n,p)*p**p*q**q*(n+2*p*q),n**(n+1))


def nest(p):
    H=F(p+17)/(F(p,p+1)+F(17,10))
    Q=F(175,128)**2*g(p)*g(17)/g(p+17)*F(27*p+17,p+17)
    return H,Q


def build():
    if hashlib.sha256(BASE.read_bytes()).hexdigest()!=PIN:
        raise RuntimeError('incorrect parent two-layer certificate hash')
    old=json.loads(BASE.read_text())
    if old['max_D']!=56 or len(old['frontiers'])!=57:
        raise RuntimeError('unexpected parent dimensions')
    E=[[(F(x['H']),F(x['Q']),x['op']) for x in row] for row in old['frontiers']]
    extension=[];summaries=[]
    for D in range(57,86):
        candidates={}
        def keep(h,q,op):
            previous=candidates.get(h)
            if previous is None or q>previous[0]:candidates[h]=(q,op)
        for i,(h,q,_) in enumerate(E[D-1]):
            keep(h+1,q,['point',D-1,i])
        for size in range(3,D+1):
            for p in range(1,(size-1)//2+1):
                q=size-1-p
                h_atom,q_atom=atom(p,q)
                for i,(h,Q,_) in enumerate(E[D-size]):
                    keep(h+h_atom,Q*q_atom,['block',D-size,i,p,q])
        front=[];best_q=F(0)
        for h,(q,op) in sorted(candidates.items(),reverse=True):
            if q>best_q:
                front.append((h,q,op));best_q=q
        E.append(front)
        extension.append([{'H':str(h),'Q':str(q),'op':op} for h,q,op in front])
        idx=max(range(len(front)),key=lambda i:front[i][0]*front[i][1])
        h,q,_=front[idx]
        summaries.append({'D':D,'states':len(front),'winner':idx,'ratio':str(h*q/F(D))})
        if D%5==0 or D==57:print('new D',D,'states',len(front),'exact two-layer optimum',h*q/F(D))
    witnesses=[]
    Q4=F(175,128)
    for D in range(56,86):
        best=None
        for p in [6,7]:
            h_n,q_n=nest(p)
            tailD=D-(p+18)
            for i,(h,q,_) in enumerate(E[tailD]):
                val=(h_n+h)*q_n*q/F(D)
                if best is None or val>best[0]:best=(val,p,tailD,i)
        Bmax=max(h*q/F(D) for h,q,_ in E[D])
        val,p,tailD,i=best
        witnesses.append({'D':D,'p':p,'tailD':tailD,'tail_index':i,
                          'lower':str(val),'two_layer_max':str(Bmax),
                          'relative_factor':str(val/Bmax)})
    result={'parent_sha256':PIN,'first_D':57,'last_D':85,
            'frontiers':extension,'summary':summaries,'witnesses55to84':witnesses}
    OUT.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('CERTIFICATE',OUT,'size',OUT.stat().st_size,'new_states',sum(len(x) for x in extension))
    print('MIN_FINITE_WITNESS_FACTOR',min(F(x['relative_factor']) for x in witnesses))
    print('STRICT_GREATER_THAN_1007/1000',all(F(x['relative_factor'])>F(1007,1000) for x in witnesses))

if __name__=='__main__':build()
