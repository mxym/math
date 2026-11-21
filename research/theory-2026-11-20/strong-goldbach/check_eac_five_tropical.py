"""Exact rational terminal checker. Read stdout of check_eac_five_tropical.cpp."""
from fractions import Fraction as F
from collections import Counter
import sys

def must(c, msg):
    if not c: raise ValueError(msg)

def line_solution(A):
    # RREF for A*w=1. Each double-singular matrix here has rank four.
    H=[[F(x) for x in row]+[F(1)] for row in A]
    piv=[]
    for j in range(5):
        z=next((i for i in range(len(piv),5) if H[i][j]),None)
        if z is None:continue
        k=len(piv); H[k],H[z]=H[z],H[k]
        H[k]=[s/H[k][j] for s in H[k]]
        for i in range(5):
            if i!=k:H[i]=[x-H[i][j]*y for x,y in zip(H[i],H[k])]
        piv.append(j)
    must(len(piv)==4,'rank not four')
    if H[4][-1]:return None
    j0=next(j for j in range(5) if j not in piv)
    w=[None]*5;w[j0]=(F(0),F(1))
    for i,j in enumerate(piv): w[j]=(H[i][-1],-H[i][j0])
    for row in A:
        must(sum(row[j]*w[j][0] for j in range(5))==1,'wrong particular solution')
        must(sum(row[j]*w[j][1] for j in range(5))==0,'wrong null direction')
    return w

def bounds(w):
    # Each inequality is a+b*t >= 0. The free coordinate t lies in [0,1].
    plus=lambda x,y:(x[0]+y[0],x[1]+y[1])
    minus=lambda x,y:(x[0]-y[0],x[1]-y[1])
    need=[minus(w[0],(F(1,6),0))]+[minus(plus(w[0],v),(F(2,3),0)) for v in w[1:]]
    nonstrict=[minus((F(1,3),0),w[0])]+[minus(v,w[0]) for v in w[1:]]+[minus((F(1),0),v) for v in w]
    lo,hi=F(0),F(1)
    for a,b in need+nonstrict:
        if b>0:lo=max(lo,-a/b)
        elif b<0:hi=min(hi,-a/b)
        elif a<0:return 'empty'
    if hi<lo:return 'empty'
    mid=(lo+hi)/2
    # A nonnegative affine function vanishing at the midpoint vanishes
    # throughout the interval (also valid for an interval of length zero).
    return 'strict' if all(a+b*mid>0 for a,b in need) else 'boundary'

actual=set(); counts=Counter(); survivors={'strict':set(),'boundary':set()}
for s in sys.stdin:
    s=s.strip()
    must(len(s)==25 and s.isdigit() and s not in actual,'bad input')
    actual.add(s); A=[list(map(int,s[i:i+5])) for i in range(0,25,5)]
    w=line_solution(A);tag='inconsistent' if w is None else bounds(w)
    counts[tag]+=1
    if tag in survivors:survivors[tag].add(s)
must(len(actual)==45,'canonical count')
must(survivors['boundary']=={'0001100101020003010030010','0000200011000203010031000'},'unexpected equality branch')
must(survivors['strict']=={'0000200011000202010021000'},'unexpected strict branches')
print(dict(sorted(counts.items())))
print('strict survivor rows, in order: 00002 00011 00020 20100 21000')
