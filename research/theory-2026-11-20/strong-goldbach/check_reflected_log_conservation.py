"""Exact checks of prime-bit geometric opening and conservation constants."""
from fractions import Fraction as F
from itertools import combinations, product

def need(x,s):
    if not x:
        raise RuntimeError(s)

ps=(2,3,5,7)
cases=0
for vals in product(range(4),repeat=4):
    supp=tuple(p for p,k in zip(ps,vals) if k)
    n=1
    for p,k in zip(ps,vals):
        n*=p**k
    divsf={}
    for k in range(len(supp)+1):
        for I in combinations(supp,k):
            d=1
            for p in I:
                d*=p
            divsf[d]=(-1)**k
    raw=sum(mu*(13-d+2*d*d) for d,mu in divsf.items())
    for r in supp:
        shift=sum(mu*((13-e+2*e*e)-(13-r*e+2*(r*e)**2))
                         for e,mu in divsf.items() if e%r)
        need(raw==shift,"exact prime bit even on higher valuation")
        cases+=1

# atanh log enclosure: log(7/5) = 2 atanh(1/6).
t=F(1,6)
lo=2*sum((t**(2*k+1)/F(2*k+1) for k in range(12)), F(0))
hi=lo+2*t**25/(25*(1-t*t))
Jlo,Jhi=lo-F(".1408"),hi-F(".1408")
need(F(".09509670")<F(".486")*Jlo<F(".486")*Jhi<F(".09509671"),
     "negative broad term")
need(F(".19508521")<F(".997")*Jlo<F(".997")*Jhi<F(".19508523"),
     "positive tiny term")
need(F("-.08998852")<F(".010")-F(".511")*Jhi
               <F(".010")-F(".511")*Jlo<F("-.08998851"),"localized threshold")
need(F(".997")-F(".486")==F(".511"),"disjoint parts")
print(cases,"exact prime-bit higher-valuation cases; all signed constants certified")
