"""Exact optimally spaced C-marked 33-set cycle kernel and formal deck census."""
from fractions import Fraction as F

def partitions(n, rem, previous, delta):
    if n == 0:
        if not rem:
            yield ()
        return
    for k in range(previous[0], n + 1):
        if k == 4:
            continue
        for j in range(min(k // 2, rem) + 1):
            if (k, j) < previous or 2*(rem-j) > n-k:
                continue
            if delta==12 and (k,j)==(3,0):  # previously excluded triangle flip
                continue
            for tail in partitions(n-k, rem-j, (k,j), delta):
                yield ((k,j),) + tail

def union_gap(deck,delta):
    D=154*22-(3*delta-22)**2
    slots={(0,0)}
    for k,j in deck:
        slots |= {(v+k,c+j) for v,c in slots}
    return all(10*(D*k*(33-k)-42*(33*j-delta*k)**2)>23*33*D
               for k,j in slots if k not in (0,33))

from functools import cache
@cache
def best(k,j):
 if not j:return F(0)
 # r_i=a_i*r0+b_i for inverse Green kernel at cyclic distance i
 a,b=[F(1),F(3,2)],[F(0),-F(1,2)]
 for i in range(2,k+1):
  a.append(3*a[-1]-a[-2]);b.append(3*b[-1]-b[-2])
 z=-b[-1]/(a[-1]-1);r=[x*z+y for x,y in zip(a,b)]
 v=[(i*k)//j for i in range(j)]
 return sum(r[(p-q)%k] for p in v for q in v)

# Rational certificate for three strict comparisons over Q(sqrt5).
# 2.23606 < sqrt5 < 2.23607; 0.38196 < (3-sqrt5)/2.
upper,alpha=F(223607,100000),F(38196,100000)
assert upper**2>5 and 2*alpha<3-upper
assert 12+2*(8*alpha**2+4*alpha**3+4*alpha**4+8*alpha**5)>20*upper/3
assert 12+20*alpha**2>20*upper/3
assert 12+2*(9*alpha**2+6*alpha**4+3*alpha**6+alpha**5)>20*upper/3
for delta,n0,n1 in ((5,7089,7089),(12,2494,1718)):
    decks=[t for t in partitions(33,delta,(3,0),delta) if union_gap(t,delta)]
    assert len(decks)==n0
    cap=F(delta*delta+4*delta+88,42)
    out=[t for t in decks if sum(best(k,j) for k,j in t)<=cap]
    assert len(out)==n1
    if delta==12:
        assert all(all(j>0 for k,j in t) for t in out)
        assert max(sum(k==3 for k,j in t)for t in out)==9
    print('overlap',delta,':',len(decks),'prior formal decks;',len(out),'pass the optimized cross-Gram test')
