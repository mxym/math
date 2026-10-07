#!/usr/bin/env python3
"""Exact d=2 regressions for the volume-weighted anchor proof.
Not a proof; all quantities use Fraction, with the infinity norm for h.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod


def cross(a,b): return a[0]*b[1]-a[1]*b[0]
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def det(a,b,c): return cross(sub(b,a),sub(c,a))
def psi(base,y,z):
    a,b=base
    fy,fz=det(a,b,y),det(a,b,z)
    return min(max(fy,0),max(-fz,0))+min(max(-fy,0),max(fz,0))
def norm(x): return max(abs(t) for t in x)
def witness(W,x):
    result=Q(0)
    for i in range(3):
        result+=psi([W[k] for k in range(3) if k!=i],W[i],x)
    for i in range(3):
        for j in range(i+1,3):
            result+=psi([x]+[W[k] for k in range(3) if k not in (i,j)],W[i],W[j])
    return result

def audit(name,law,expected):
    assert sum(law.values())==1
    assert all(sum(p*x[k] for x,p in law.items())==0 for k in range(2))
    pts=list(law)
    diameter=max(norm(sub(x,y)) for x in pts for y in pts)
    A=sum(law[x]*law[y]*abs(cross(x,y)) for x,y in product(pts,repeat=2))
    B=V2=EH=EHpos=EHsing=Q(0)
    choices=[]
    for W in product(pts,repeat=3):
        probability=prod(law[w] for w in W)
        signed=det(*W); V=abs(signed)
        H=sum(p*witness(W,x) for x,p in law.items())
        B+=probability*V; V2+=probability*V*V; EH+=probability*H
        if not V:
            EHsing+=probability*H
            continue
        EHpos+=probability*H
        h=Q(0)
        for x,p in law.items():
            alpha=[]
            for i in range(3):
                replacement=list(W); replacement[i]=x
                alpha.append(det(*replacement)/signed)
            assert sum(alpha)==1
            r=max(range(3),key=lambda i:alpha[i])
            N=sum(max(-a,0) for a in alpha)
            U=sum(max(alpha[i],0) for i in range(3) if i!=r)
            phi=sum(min(1,max(-a,0)) for a in alpha)
            phi+=sum(min(max(alpha[i],0),max(alpha[j],0)) for i in range(3) for j in range(i+1,3))
            assert min(1,N+U)<=phi
            assert norm(sub(x,W[r]))<=diameter*phi
            assert V*phi<=witness(W,x)
            h+=p*norm(sub(x,W[r]))
        assert h<=diameter*H/V
        choices.append((H/V,h,V,W,probability))
    D=B-A
    assert D>=0 and EH<=6*D
    assert EH==EHpos+EHsing
    assert sum(probability*V/B for _,_,V,_,probability in choices)==1
    assert sum((probability*V/B)*ratio for ratio,_,V,_,probability in choices)==EHpos/B
    chosen=min(choices,key=lambda c:(c[0],c[1]))
    assert chosen[0]<=6*D/B
    assert chosen[1]<=diameter*6*D/B
    got={'A':A,'B':B,'D':D,'EV2':V2,'EHsing':EHsing}
    for key,value in expected.items(): assert got[key]==value,(name,key,got[key],value)
    print(name)
    print('  '+', '.join(f'{key}={value}' for key,value in got.items()))
    print(f'  E_V[H/V]={EHpos/B}; 6D/B={6*D/B}; chosen H/V={chosen[0]}, h_inf={chosen[1]}')
    return got

if __name__=='__main__':
    for t in (Q(1,4),Q(1,100),Q(1,10000)):
        a,b,c=(Q(1),Q(0)),(Q(0),Q(1)),(-t,-t)
        base={a:t/(1+2*t),b:t/(1+2*t),c:1/(1+2*t)}
        A0=6*t*t/(1+2*t)**2
        audit(f'rare triangle t={t}',base,{'A':A0,'B':A0,'D':0,'EV2':6*t*t/(1+2*t)})
        eta=Q(1,100)
        mixture={x:(1-eta)*p for x,p in base.items()}; mixture[(Q(0),Q(0))]=eta
        audit(f'rare triangle plus center t={t}, eta={eta}',mixture,
              {'A':(1-eta)**2*A0,'B':(1-eta)**2*(1+2*eta)*A0,
               'D':2*eta*(1-eta)**2*A0,'EV2':6*t*t*(1-eta)**2/(1+2*t)})
    for s in (Q(1),Q(1,100),Q(1,10000)):
        law={(a,b*s):Q(1,4) for a,b in product((Q(-1),Q(1)),repeat=2)}
        audit(f'flat rectangle s={s}',law,{'A':s,'B':3*s/2,'D':s/2,'EV2':6*s*s})
    law={x:Q(1,5) for x in ((Q(0),Q(0)),(Q(1),Q(0)),(Q(-1),Q(0)),(Q(0),Q(1)),(Q(0),Q(-1)))}
    audit('cross plus origin, including singular positive H',law,
          {'A':Q(8,25),'B':Q(72,125),'D':Q(32,125),'EV2':Q(24,25),'EHsing':Q(24,625)})
    print('All exact checks passed.')
