from fractions import Fraction as Q
from itertools import combinations


def req(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def poly(J):
    C=[Q(1,4)]+[Q(1,4*j*(J-1)) for j in range(2,J+1)]
    A=1+sum(C)
    req(sum(2*j*c for j,c in enumerate(C,1))==1,('normal',J))
    def f(t):
        u=1-2*t
        return A*u-sum(c*u**(2*j+1) for j,c in enumerate(C,1))
    return f


def rows(t):
    for k in range(len(t)+1):
        for ix in combinations(range(len(t)),k):
            yield (-1)**k,sum((t[i] for i in ix),Q())


# Exact top-level rail checks; piecewise-linear minimum is concave, so minima
# over the entire short-prime band occur at its two endpoints.
rail=lambda nu:min((1+nu)/2,(4-6*nu)/7)
req(min(rail(Q(1,100)),rail(Q(7,100)))==Q(505,1000),'Fouvry')
for kap in (Q(1,1000), Q(1,10000),Q(1,100000)):
    req(Q(504,1000)+Q(2,5)*kap<Q(505,1000),'marked rail')

def parts(total,k,lo=1):
    if k==1:
        if total>=lo:
            yield (total,)
        return
    for lead in range(lo,total//k+1):
        for tail in parts(total-lead,k-1,lead):
            yield (lead,)+tail

f=poly(6)
checked_odd=checked_even=0
for rank in range(3,10):
    for num in parts(24,rank):
        t=tuple(Q(k,24) for k in num)
        half=sum(mu*f(s) for mu,s in rows(t) if s<Q(1,2))
        if rank%2==1:
            full=sum(mu*f(s) for mu,s in rows(t))
            req(full==2*half and half<0, ('odd',t))
            checked_odd+=1
        if rank%2==0 and 0<Q(1,2)-t[-1]<t[0]:
            full_core=sum(mu*f(s) for mu,s in rows(t[:-1]))
            req(half==full_core-2*f(t[-1]) and full_core<0 and half<0,('near-half-even',t))
            checked_even+=1
req(checked_odd and checked_even,(checked_odd,checked_even))
print(f'Exact rational profiles: {checked_odd} odd, {checked_even} marked near-half even.')
