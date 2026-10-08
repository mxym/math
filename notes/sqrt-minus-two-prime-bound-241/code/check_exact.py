#!/usr/bin/env python3
"""Exact layered 19/5 rational-prime sieve checker (no solver/floats).

Uses the SHA256-pinned, independently certified period-1122 finite
component partition as input. Exhausts all needed CRT shift states.
"""
from pathlib import Path
import gzip
import hashlib
import json

HERE=Path(__file__).resolve().parent
PARENT=HERE.parents[1]/'sqrt-minus-two-sqrt6-period'/'code'
P_POS=PARENT/'positive_q1122.json.gz'
P_EXC=PARENT/'exceptional_closure.json'
POS_SHA='86f44f88613a6e7f3f4808c6611ac76bd689b1d876eea27f10cf29eb953df314'
EXC_SHA='b4b5c81b3a566a038c859e005146f6076326f5eee4c76afd0406a347989e41e6'
Q=1122
B=241
P19=19
P5=5
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))


def require(ok,why):
    if not ok:raise ValueError(why)


def norm(z):
    a,b=z
    return a*a+2*b*b


def read_source():
    require(P_POS.exists() and P_EXC.exists(),'predecessor certificates unavailable')
    require(hashlib.sha256(P_POS.read_bytes()).hexdigest()==POS_SHA,
            'positive parent certificate hash mismatch')
    require(hashlib.sha256(P_EXC.read_bytes()).hexdigest()==EXC_SHA,
            'exceptional closure parent certificate hash mismatch')
    with gzip.open(P_POS,'rt',encoding='ascii') as f:parent=json.load(f)
    require(set(parent)=={'q','components'} and parent['q']==Q,
            'wrong upstream quotient period')
    groups=parent['components']
    require(len(groups)==6688 and sum(map(len,groups))==204800,
            'wrong upstream finite component count')
    return groups,json.loads(P_EXC.read_text())


def extra_exceptional_check(closure):
    C={tuple(z) for z in closure}
    require(len(C)==92 and len(closure)==92,'wrong inherited exceptional closure')
    p19={(a,b) for a in (-1,1) for b in (-3,3)}
    inert5={(-5,0),(5,0)}
    require(p19 | inert5 <= C, 'exceptional factors outside original 90-prime component')
    require(all(norm(z)==19 for z in p19),'incorrect split factors of 19')
    require(all(norm(z)==25 for z in inert5),'incorrect inert elements over 5')
    # -2 is a quadratic nonresidue mod 5; hence 5 | N(a,b) forces
    # 5|a and 5|b. At 19, +/-6 are the square roots of -2.
    for a in range(19):
        for b in range(19):
            require((norm((a,b))%19==0)==((a+6*b)%19==0 or (a-6*b)%19==0),
                    'split norm-19 congruence failed')
    for a in range(5):
        for b in range(5):
            require((norm((a,b))%5==0)==(a==0 and b==0),
                    'inert norm-5 congruence failed')
    print('EXCEPTIONS: six new norm-19/inert-5 prime elements lie inside the certified 90-prime component')


def adjacency(points):
    index={point:i for i,point in enumerate(points)}
    require(len(index)==len(points),'non-distinct parent component points')
    return [tuple(index.get((x+da,y+db),-1) for da,db in F)
            for x,y in points]


def connected_parts(present,edges):
    """List *actual vertex-index sets* of connected components."""
    m=len(present)
    visited=bytearray(m)
    for root in range(m):
        if not present[root] or visited[root]:continue
        queue=[root]
        visited[root]=1
        for j in queue:
            for v in edges[j]:
                if v>=0 and present[v] and not visited[v]:
                    visited[v]=1
                    queue.append(v)
        yield queue


def check(groups):
    require(Q%19==1 and (Q*19)%5==3,'coprime-period CRT arithmetic failed')
    allowed19=[[int((x*x+2*y*y)%19!=0) for y in range(19)] for x in range(19)]
    parent_large=0;shifts19=0;first_oversized=0;max19=0
    max5=0;shifts5=0;witness=None
    for group_id,seq in enumerate(groups):
        if len(seq)<=B:continue
        parent_large+=1
        coords=[tuple(p) for p in seq]
        edges=adjacency(coords)
        xm=[x%19 for x,y in coords]
        ym=[y%19 for x,y in coords]
        m=len(coords)
        for sx in range(19):
            mx=[(x+sx)%19 for x in xm]
            for sy in range(19):
                shifts19+=1
                present=bytearray(allowed19[mx[i]][(ym[i]+sy)%19]
                                  for i in range(m))
                for comp in connected_parts(present,edges):
                    if len(comp)>max19:max19=len(comp)
                    if len(comp)<=B:continue
                    first_oversized+=1
                    # z = x+Q*(s19+19*s5), independently in both coordinates;
                    # complete CRT representatives s5=0,...,4 cover all
                    # translated components under the enlarged period Q*19*5.
                    for ux in range(5):
                        xmod={i:(coords[i][0]+Q*(sx+19*ux))%5 for i in comp}
                        for uy in range(5):
                            shifts5+=1
                            fine=bytearray(m)
                            for i in comp:
                                y=(coords[i][1]+Q*(sy+19*uy))%5
                                fine[i]=int((xmod[i]*xmod[i]+2*y*y)%5!=0)
                            for part in connected_parts(fine,edges):
                                count=len(part)
                                require(count<=B,
                                        'counterexample: refined prime sieve component exceeds 241')
                                if count>max5:
                                    max5=count
                                    witness=(group_id,sx,sy,ux,uy)
    require(parent_large==190,'number of predecessor components over 241 changed')
    require(shifts19==parent_large*19*19,'incomplete mod19 shift coverage')
    require(first_oversized==8 and max19==298,
            'unexpected first-stage component spectrum')
    require(shifts5==first_oversized*5*5,'incomplete second-stage CRT shifts')
    require(max5==241 and witness==(2228,15,0,1,0),
            'sharp refined upper-bound witness incorrect')
    print('REFINEMENT: first-stage groups',parent_large,
          'mod19 shifts',shifts19,'large mod19 pieces',first_oversized,
          'max mod19',max19)
    print('REFINEMENT: second-stage checks',shifts5,
          'maximum component',max5,'witness',witness)
    print('EXACT BOUND: every nonexceptional irreducible component has <=241 vertices')
    print('ALL EXACT CERTIFICATES VERIFIED')


if __name__=='__main__':
    groups,closure=read_source()
    extra_exceptional_check(closure)
    check(groups)
