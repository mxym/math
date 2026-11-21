"""Exact rails, prefix multiplicities, and affine remaining-cofactor identity."""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

for D,E in ((F(".002"),F(".002")), (F(".00402"),F(".00221"))):
    maxima=[F(0),F(0)]
    for sigma,b,d,e,g in product((F(".10"),F(".14")),(F(".4999"),F(".500")),
             (0,D),(0,E),(0,F(".0001"))):
        a=(1-sigma)/2
        z=F(".0002")
        t=a+b+sigma+d+e+g-1+z
        need(t<sigma and sigma+t<b,"frequency separation")
        diag=1+(a+b+d+e-1-g+z)/2
        off=a/2+sigma+5*b/4+d+3*e/2+z
        maxima=[max(maxima[0],diag), max(maxima[1],off)]
    need(maxima[0]<F(".979") and maxima[1]<F(".988"),
         "profile ceilings")
    print("Exact diagonal and off-diagonal:", *(float(u) for u in maxima))

p0=(3,5,7,11,13,17,19,23)
ccases=0
for n in range(9):
    for ps in combinations(p0,n):
        for limit in (1,2,5,15,65,77,143,999,5000):
            cross=None; d=1
            for p in ps:
                if d*p>limit:
                    cross=p
                    break
                d*=p
            if cross is None:
                need(d==prod(ps),"complete prefix")
            else:
                d0=d*cross
                need(d<=limit<d0<=limit*cross and
                     tuple(p for p in ps if p<=cross)==tuple(p for p in ps if d0%p==0),
                     "first crossing; largest prime recovers label")
            ccases+=1

lap=0
for k1,k2,k3 in product(range(4),repeat=3):
    exps=(k1,k2,k3)
    support=tuple(i for i,k in enumerate(exps) if k)
    if not support:
        continue
    s0=0; sl=[0]*3
    for n in range(len(support)+1):
        for I in combinations(support,n):
            mu=(-1)**n
            s0+=mu
            for i in I:
                sl[i]+=mu
    need(s0==0 and tuple(-v for v in sl)==tuple(int(support==(i,)) for i in range(3)),
         "flat zero and exact Lambda on all affine cofactors")
    lap+=1
print(ccases,"prefix cases;",lap,"affine cofactor checks")
