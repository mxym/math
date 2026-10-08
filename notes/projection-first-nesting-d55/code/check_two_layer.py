#!/usr/bin/env python3
"""Independent exact checker for complete two-layer join frontiers D<=56."""
import bisect
import json
from pathlib import Path
from fractions import Fraction as F
from math import comb

ROOT=Path(__file__).resolve().parent.parent

def require(x,msg):
    if not x:raise RuntimeError('two-layer verifier: '+msg)

def frac(v,allow_zero=False):
    require(isinstance(v,str),'rational not string')
    q=F(v)
    require(str(q)==v and (q>=0 if allow_zero else q>0),'noncanonical fraction')
    return q

def atom(p,q):
    n=p+q
    return F(n)/(F(p,p+1)+F(q,q+1)),F(comb(n,p)*p**p*q**q*(n+2*p*q),n**(n+1))

def dominates(h,q,level):
    keys=[-t[0] for t in level]
    i=bisect.bisect_right(keys,-h)-1
    return i>=0 and level[i][1]>=q

def check(filename=None,quiet=False):
    raw=json.loads(Path(filename or ROOT/'certificates/two_layer56.json').read_text())
    require(raw['max_D']==56 and len(raw['frontiers'])==57 and len(raw['summary'])==56,
            'incomplete certificate')
    fs=[];count=0
    for D,row in enumerate(raw['frontiers']):
        level=[]
        for st in row:
            require(set(st)=={'H','Q','op'},'fields')
            h=frac(st['H'],allow_zero=D==0);q=frac(st['Q'])
            op=st['op']
            require(isinstance(op,list),'malformed operation')
            if D==0:
                require(len(row)==1 and op==['empty'] and h==0 and q==1,'empty base')
            else:
                require(op[0] in ['point','block'],'invalid operation kind')
                if op[0]=='point':
                    require(len(op)==3 and op[1]==D-1,'point op dimension')
                    prior,i=op[1:]
                    require(isinstance(i,int) and not isinstance(i,bool) and 0<=i<len(fs[prior]),'point pointer')
                    hh,qq=fs[prior][i][:2];hh+=1
                else:
                    require(len(op)==5,'block pointer length')
                    prior,i,p,t=op[1:]
                    require(all(isinstance(v,int) and not isinstance(v,bool) for v in (prior,i,p,t)), 'integer pointers')
                    require(1<=p<=t and prior==D-p-t-1 and 0<=prior<D,'block dimensions')
                    require(0<=i<len(fs[prior]),'block parent pointer')
                    ha,qa=atom(p,t);hh,qq=fs[prior][i][:2]
                    hh+=ha;qq*=qa
                require((h,q)==(hh,qq),f'unattainable state at D={D}')
                require(F(0)<h<=D,'H bounds')
            level.append((h,q,op))
        require(level and all(level[i][0]>level[i+1][0] and level[i][1]<level[i+1][1]
                      for i in range(len(level)-1)),f'non-Pareto at D={D}')
        fs.append(level)
        if D==0:continue
        negkeys=[-v[0] for v in level];values=[v[1] for v in level]
        def covered(h,q):
            idx=bisect.bisect_right(negkeys,-h)-1
            return idx>=0 and values[idx]>=q
        for h,q,_ in fs[D-1]:
            require(covered(h+1,q),f'point operation uncovered D={D}')
            count+=1
        for T in range(3,D+1):
            for p in range(1,(T-1)//2+1):
                q=T-1-p
                ha,qa=atom(p,q)
                for h,v,_ in fs[D-T]:
                    require(covered(h+ha,v*qa),f'block operation uncovered D={D},p={p},q={q}')
                    count+=1
        row_summary=raw['summary'][D-1]
        require(row_summary['D']==D and row_summary['frontier_size']==len(level),'summary size')
        i=row_summary['winning_index']
        require(isinstance(i,int) and 0<=i<len(level),'winning pointer')
        ratios=[h*q/F(D) for h,q,_ in level]
        require(F(row_summary['sharp_ratio'])==max(ratios)==ratios[i],f'false optimum D={D}')
    # Direct exact witness checks without trusting stored construction pointers.
    Q5=F(189,128);H56,Q56=atom(5,6)
    expected=(F(4)*F(6)+H56)*Q5**4*Q56/F(56)
    claimed=F(raw['summary'][55]['sharp_ratio'])
    require(claimed==expected==F(9444402294359878125,2393367762580799488),
            'sharp 55D two-layer extremum wrong')
    if not quiet:
        print('PASS: complete two-layer join Pareto frontiers through D=56')
        print('attained Pareto states =',sum(len(t) for t in fs))
        print('exact join/atom closure checks =',count)
        print('sharp two-layer 55D ratio =',claimed)
        print('optimal 55D two-layer witness = 4 B(5,5) joins and 1 B(5,6)')
    return [F(x['sharp_ratio']) for x in raw['summary']]

if __name__=='__main__':check()
