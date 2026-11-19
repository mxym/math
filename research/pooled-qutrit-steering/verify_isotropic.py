#!/usr/bin/env python3
"""Exact finite arithmetic checks, not a substitute for the compactness/rigidity proof."""
from fractions import Fraction as Q
from itertools import product, combinations_with_replacement
from math import comb
def ck(condition, label):
    if not condition:
        raise ArithmeticError(label)
def pos(x):
    return max(0,x)
# The Dirichlet integral's three truncated powers integrate to 1/(3j).
m=sum(Q((-1)**(j+1)*comb(3,j),3*j) for j in range(1,4))
ck(m==Q(11,18) and (3*m-1)/2==Q(5,12),"Haar normalization")
rows = sorted(set(tuple(sorted((Q(a,6),Q(b,6),Q(6-a-b,6))))
                  for a in range(7) for b in range(7-a)))
ensembles=cutoffchecks=0
for trip in combinations_with_replacement(rows,3):
    for masses in [(1,1,1),(1,2,4),(3,1,2)]:
        wt=[Q(w,sum(masses)) for w in masses]
        alpha=sum(w*r[2] for w,r in zip(wt,trip))
        vals=[(p,w) for w,r in zip(wt,trip) for p in r]
        remaining=Q(1); best=Q(0)
        for p,w in sorted(vals,reverse=True):
            x=min(remaining,w); best+=x*p; remaining-=x
        ck(remaining==0,'fractional selection')
        targets=sorted({Q(0),Q(1),*(p for p,w in vals)})
        scores=[]
        for t in targets:
            s=t+sum(w*pos(p-t) for p,w in vals)
            excess=sum(w*(pos(t-r[2])+pos(r[1]-t)+pos(r[0]-t))
                       for w,r in zip(wt,trip))
            ck(s-alpha==excess,'excess')
            ck((excess==0)==all(r[1]<=t<=r[2] for r in trip),'support interval')
            scores.append(s); cutoffchecks+=1
        ck(min(scores)==best and best>=alpha,'cutoff')
        ensembles+=1
# Orthogonal matrices I-2vv^T/(v^Tv), followed by phase tests in Q(i).
# Inputs (1,u,v)/sqrt(3); the unscaled squared outputs must sum to three.
phases={(Q(-1),Q(0))}
for t in [Q(k,3) for k in range(-5,6)]+[Q(k) for k in range(-4,5)]:
    phases.add(((1-t*t)/(1+t*t),2*t/(1+t*t)))
phases=sorted(phases)
mats=[]
cases=dict(block=0,onezero=0,dense=0)
for h in combinations_with_replacement(range(4),3):
    d=sum(x*x for x in h)
    if d==0: continue
    U=[[Q(int(i==j))-Q(2*h[i]*h[j],d) for j in range(3)] for i in range(3)]
    mats.append(U)
# R12 R23 has exactly one zero if both angles have nonzero sine and cosine.
for t in (Q(1,2),Q(1,3),Q(2,3)):
    c,s=(1-t*t)/(1+t*t),2*t/(1+t*t)
    mats.append([[c,-s*c,s*s],[s,c*c,-c*s],[Q(0),s,c]])
for U in mats:
    ck(all(sum(U[i][k]*U[j][k] for k in range(3))==int(i==j)
           for i in range(3) for j in range(3)),'orthonormal')
    block=any(abs(x)==1 for row in U for x in row)
    zero=sum(x==0 for row in U for x in row)
    witness=False
    for u,v in product(phases,repeat=2):
        ps=[(a+b*u[0]+c*v[0])**2+(b*u[1]+c*v[1])**2 for a,b,c in U]
        ck(sum(ps)==3,'unitarity on phases')
        if sum(x>1 for x in ps)>=2:
            witness=True
            break
    ck(witness != block,'tested flat torus implication')
    cases['block' if block else ('onezero' if zero else 'dense')]+=1
# Eisenstein integer coordinates 1,omega with omega^2=-1-omega and |a+b omega|^2=a^2-ab+b^2.
omega=[(1,0),(0,1),(-1,-1)]
probs=[]
for i in range(3):
    a,b=(sum(s*omega[(i*j)%3][k] for j,s in enumerate([1,1,-1])) for k in range(2))
    probs.append(Q(a*a-a*b+b*b,9))
ck(probs==[Q(1,9),Q(4,9),Q(4,9)],'Fourier exception')
ck(all(cases.values()),'nontrivial finite test')
# In the independent short proof, rephase a row to real nonnegative entries.
# Evaluate the third-root orbit of the deviation on every magic sign centre.
pos_centres=0
for a,b,c in product(range(5),repeat=3):
    if sum(k!=0 for k in (a,b,c))<2:
        continue
    # At the real centre D is real, and the three real deviations are 2D,-D,-D.
    terms=(a*b,b*c,c*a)
    m0=min(range(3),key=lambda i: terms[i])
    signs=tuple(1 if j==m0 else -1 for j in range(3))
    u,v=signs[0],signs[2]
    ck((u,u*v,v)==signs,'real sign centre')
    D=sum(s*q for s,q in zip(signs,terms))
    ck(D<0,'strict second positive branch')
    ck(sum(d>0 for d in (2*D,-D,-D))==2,'orbit')
    pos_centres+=1
print('Strict real sign centres:',pos_centres)
print('Haar max =',m,'; physical baseline =',(3*m-1)/2)
print('Fractional menus:',ensembles,'cutoff/excess/interval checks:',cutoffchecks)
print('Rational orthogonal cases:',cases,'using',len(phases),'exact rational phases')
print('Fourier probabilities:',','.join(map(str,probs)))
