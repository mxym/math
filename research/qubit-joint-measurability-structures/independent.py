#!/usr/bin/env python3
"""Exact independent certificate tests on every labeled complex through four vertices.
The checker enumerates downward-closed face sets, not facet collections. No solver,
floating arithmetic, dependencies or Python assertions; -O is safe.
"""
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
from math import prod

def ck(test, msg):
    if not test:
        raise ArithmeticError(msg)
I = (F(1),F(0),F(1))
O = (F(0),)*3
def mul(t,x): return tuple(t*v for v in x)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def fold(v):
    a=O
    for x in v: a=add(a,x)
    return a
def det(x): return x[0]*x[2]-x[1]*x[1]
def positive(x): return x[0]>=0 and x[2]>=0 and det(x)>=0
def proj(x,y): return tuple(F(z,x*x+y*y) for z in (x*x,x*y,y*y))

def review(n):
    counts=Counter()
    sub=range(1<<n)
    base={0}|{1<<i for i in range(n)}
    opt=sorted(set(sub)-base)
    for mask in range(1<<len(opt)):
        k=base|{s for j,s in enumerate(opt) if mask>>j&1}
        if any((s^(1<<i)) not in k for s in k for i in range(n) if s>>i&1):
            continue
        counts['K']+=1
        if n==0:
            ck(k=={0},'empty complex');counts['faces']+=1;continue
        facets=[s for s in sorted(k) if all((s|(1<<i)) not in k for i in range(n) if not s>>i&1)]
        m=len(facets); w=F(2,2*m-1); eps=F(1,2*n*(2*m-1))
        p={}
        for j in range(m+n):
            a,b=m+n+1,j+1
            for s,(u,v) in enumerate(((a,b),(-b,a))):
                p[2*j+s]=proj(u,v)
            ck(add(p[2*j],p[2*j+1])==I,'orthobasis')
        ck(all(positive(x) and det(x)==0 and x[0]+x[2]==1 for x in p.values()),'projector')
        ck(len(set(p.values()))==len(p),'distinct ranges')
        weights={v:mul(w if v<2*m else eps,P) for v,P in p.items()}
        settings=[]
        for i in range(n):
            marks={2*j+s for j,f in enumerate(facets) if not f>>i&1 for s in (0,1)}
            marks.update({2*(m+i),2*(m+i)+1})
            pi={v:weights[v] for v in marks};pi[-1]=add(I,mul(-1,fold(pi.values())))
            ck(len(pi)<=2*m+1 and all(positive(x) for x in pi.values()) and fold(pi.values())==I,'POVM')
            ck(det(pi[-1])>0,'null full rank')
            settings.append(pi)
        for i in range(n):
            for k2 in range(n):
                if i==k2: continue
                priv=p[2*(m+i)]
                ck(all(det(add(priv,T))>0 for T in settings[k2].values()),'no prior support for a stochastic postprocessing')
        for s in sub:
            ix=[i for i in range(n) if s>>i&1]
            if s in k:
                counts['faces']+=1
                labels=set().union(*(set(settings[i]) for i in ix))-{-1}
                g={v:weights[v] for v in labels}
                g[-1]=add(I,mul(-1,fold(g.values())))
                ck(all(positive(T) for T in g.values()) and fold(g.values())==I,'parent')
                ck(g[-1][0]==g[-1][2] and g[-1][1]==0 and g[-1][0]>=F(1,2*(2*m-1)),'face margin')
                for i in ix:
                    marginal={z:O for z in settings[i]}
                    for v,T in g.items():
                        out=v if v in marginal else -1
                        marginal[out]=add(marginal[out],T)
                    ck(marginal==settings[i],'full parent marginals');counts['marginals']+=1
            else:
                counts['nonfaces']+=1
                # Extract one full lossy basis per facet by stochastic coarse graining.
                marginal=[]
                for j in range(m):
                    owner=next(i for i in ix if 2*j in settings[i])
                    pi=settings[owner]
                    ck(fold(T for z,T in pi.items() if z not in {2*j,2*j+1})==mul(1-w,I),'lossy basis coarse-graining')
                    for b in range(2): marginal.append(pi[2*j+b])
                # Ranges of all marginal rank-1 effects are distinct, hence disjoint
                # at every nonzero parent atom. det(U+V)>0 is an exact ray test.
                ck(all(positive(T) and det(T)==0 for T in marginal),'selected PSD rank one')
                ck(all(det(add(U,V))>0 for U,V in combinations(marginal,2)),'ray intersection')
                ck(fold(marginal)==mul(m*w,I) and m*w>1,'nonface overcount')
    return counts

for n,wanted in enumerate([1,1,2,9,114]):
    c=review(n);ck(c['K']==wanted,'number of full-vertex complexes')
    print('n=%d K=%d faces=%d nonfaces=%d full_marginal_checks=%d'%(n,c['K'],c['faces'],c['nonfaces'],c['marginals']))
