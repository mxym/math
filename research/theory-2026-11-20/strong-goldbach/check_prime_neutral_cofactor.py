from fractions import Fraction as F
from itertools import combinations
from math import prod


def need(ok, x):
    if not ok:
        raise ArithmeticError(x)


def rows(parts):
    for k in range(len(parts)+1):
        for ids in combinations(range(len(parts)),k):
            yield (-1)**k,sum((parts[i] for i in ids),F(0))


def parts(n,k,lo=1):
    if k==1:
        if n>=lo:
            yield (n,)
        return
    for t in range(lo,n//k+1):
        for r in parts(n-t,k-1,t):
            yield (t,)+r


def score(f,t):
    return sum(mu*(f(s)-1) for mu,s in rows(t) if s<F(1,2))


kap=F(1,2000)
J=8  # Small illustrative degree; the theorem takes J=ceil(1/kappa).
c=[(1-kap)/2]+[kap/F(2*j*(J-1)) for j in range(2,J+1)]
a=1+sum(c)
need(sum(2*j*d for j,d in enumerate(c,1))==1,'normalization')

def f(t):
    u=1-2*t
    return a*u-sum(d*u**(2*j+1) for j,d in enumerate(c,1))

need(f(F(0))==1 and score(f,(F(1),))==0,'prime atom')
need(F(504,1000)+F(14,10)*kap<F(505,1000),'modulus margin')
checked_balanced=checked_giant=0
for rank in range(3,9):
    for ps in parts(21,rank):
        t=tuple(F(p,21) for p in ps)
        s=score(f,t)
        if rank==3 and t[-1]<F(1,2):
            need(s>=2-12*prod(t)>=F(14,9),('balanced',t,s))
            checked_balanced+=1
        if t[-1]>F(1,2):
            core=sum(mu*f(ab) for mu,ab in rows(t[:-1]))
            need(s==core<0,('giant',t,s,core))
            checked_giant+=1
need(checked_balanced>0 and checked_giant>0,(checked_balanced,checked_giant))
print(f'Exact prime atom, Fouvry margin, {checked_balanced} balanced and {checked_giant} giant profiles.')
