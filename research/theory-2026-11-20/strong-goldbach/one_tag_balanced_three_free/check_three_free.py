#!/usr/bin/env python3
"""Exact algebra and exponent replay. No numerical trace estimate is asserted."""
from fractions import Fraction as F
from itertools import product
from math import comb, gcd, prod


def check(cond, detail):
    if not cond:
        raise ArithmeticError(detail)


def pf(n):
    v = []
    i = 2
    while i*i <= n:
        k = 0
        while n % i == 0:
            n //= i
            k += 1
        if k:
            v.append((i, k))
        i += 1
    if n > 1:
        v.append((n, 1))
    return v


def divs(v):
    return [prod(t) for t in product(*(tuple(p**j for j in range(k+1)) for p,k in v))]


def mu(n, j):
    ans = 1
    for _, k in pf(n):
        if k > j:
            return 0
        ans *= (-1)**k * comb(j, k)
    return ans


def fourier_counts(p, h, t):
    ans = [0]*p
    for a, b in product(range(1, p), repeat=2):
        c = t*pow(a*b,-1,p) % p
        ans[(h[0]*a+h[1]*b+h[2]*c)%p] += 1
    return ans


# A rational combination of 1,zeta_p,... has integer value V iff its
# cyclotomic coefficient vector, after subtracting V at 0, is constant.
def value_check(counts, v):
    return counts[0]-v == counts[1] and all(x == counts[1] for x in counts[2:])


def trace_cases():
    visits = 0
    for p in [2,3,5,7,11]:
        counts = [0]*p
        for u,v in product(range(1,p),repeat=2):
            counts[(v+pow(u*v,-1,p))%p] += 1
        check(value_check(counts,1), ("zero local trace numerator",p))
        for h in product(range(p),repeat=3):
            if 0 not in h:
                continue
            j = h.count(0)
            rams = prod((p-1) if v == 0 else -1 for v in h)
            val = [None,1,-(p-1),(p-1)**2][j]
            check(rams == val*(p-1),("Ramanujan model",p,h))
            for t in range(1,p):
                check(value_check(fourier_counts(p,h,t),val),("zero coordinate",p,h,t))
                visits += 1
    # CRT mask powers: product of coordinate divisors and true prefactor.
    for masks in product(range(8),repeat=4):
        q = d = q1 = q2 = q3 = 1
        g = [1,1,1]
        for p,w in zip([2,3,5,7],masks):
            q *= p
            j = [bool(w & 1<<i) for i in range(3)]
            for i,hit in enumerate(j):
                if hit:
                    g[i] *= p
            if sum(j) == 0: d *= p
            if sum(j) == 1: q1 *= p
            if sum(j) == 2: q2 *= p
            if sum(j) == 3: q3 *= p
        B = q1*q1*q2
        check(prod(g) == q1*q2*q2*q3**3,("coordinate divisor",masks))
        check(q**3//prod(g) == d**3*B,("dual volume",masks))
        check(F(d*q2*q3*q3,q*q) == F(1,d*B),("normalized trace",masks))
    return visits,8**4


def rail_check():
    q=F(532,1000)
    numerator=F(427,1000)
    cutoff_c=F(1,1000)
    xi=F(1,100000)
    spec=F(498,1000)
    Lmax=F(430,1000)
    check(1-2*Lmax == F(140,1000),"minimum primal scale")
    check(q*(1-cutoff_c)>F(531,1000),"max physical A after c")
    check(Lmax*(1-cutoff_c)>numerator,"max free lengths after c")
    check(2*q-(1-Lmax)+2*xi < spec,"long glued length")
    check((3*q-1+3*xi)/3 < spec/2,"short dual length")
    check(F(2,3)-F(5,4)*q==F(1,600),"first final saving")
    check(1-F(15,8)*q==F(1,400),"second final saving")
    check(F(1,2)+F(31,1000)+F(304,1000)<1,"base diagonal")
    check(F(5,4)*F(532,1000)<F(766,1000),"base off diagonal")
    check(F(82,1000)+F(3,2)*F(532,1000)<1,"base two free")
    check(sum((-1)**(j-1)*comb(5,j)*comb(j-1,2) for j in range(3,6))==1,"HB coefficient")
    lo=2-F(8,10)*F(11,10)
    hi=2-F(65,100)
    check(lo>1 and hi<F(3,2),"physical window")
    # lower I_k boundary largest at k=Y; upper smallest at k=1.1Y.
    check(F(122,100)>2-F(8,10) and F(126,100)<2-F(65,100)*F(11,10),"common positive window")
    check(F(918,1000)-numerator==F(491,1000),"base cutoff disjoint")
    check(F(766,1000)-numerator/2>F(491,1000),"base first cutoff disjoint")
    check(3*F(332,1000)<1<3*F(340,1000),"angular interval")


def physical_replay():
    checked = [0,0]
    for ps in [(p,q) for p in [13,17,19,23,29,31,37] for q in [43,47,53,59,67,71]] + [
        (p,q,r) for p in [41,43,47,53,59] for q in [61,67,71,73,79] for r in [83,89,97,101,103]]:
        y=prod(ps)
        x=9*y//11                         # y/x approx 1.22, interior.
        ds=divs([(p,1) for p in ps])
        K=[0]*len(ps); B=[0]*len(ps); G=[0]*len(ps)
        def idx(v):
            return [int(v%p==0) for p in ps]
        for s in ds:
            if s==1:
                continue
            r=y//s
            if not r**1000>x**505:
                continue
            for j,t in enumerate(idx(s)):
                K[j]+=t*mu(r,1)
            for a in ds:
                if r%a or not (a**1000*s**500>x**766 or (a*s)**1000>x**918):
                    continue
                c=r//a
                for j,t in enumerate(idx(s)):
                    B[j]-=t*mu(c,2)
            if s**1000>x**427:
                continue
            for a in ds:
                if r%a or max(a,r//a)**1000>x**427:
                    continue
                for j,t in enumerate(idx(s)):
                    # c <= x^.001 is c=1 on all these sampled y.
                    G[j]+=t
        if len(ps)==2:
            check(K==B and G==[0,0],("physical semiprime",ps,K,B,G))
            checked[0]+=1
        if len(ps)==3 and max(ps)**1000<=x**427:
            check(K==[1]*3 and B==[-1]*3 and G==[2]*3,("physical balanced triprime",ps,K,B,G))
            checked[1]+=1
    check(min(checked)>0,"no tested physical ranks")
    return checked


if __name__=="__main__":
    rail_check()
    print("exact local / CRT mask cases:",*trace_cases())
    print("prime-coordinate score cases:",*physical_replay())
    print("all rational rails and exact combinatorial identities verified")
