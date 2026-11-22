"""Exact arithmetic for the one-marker angular barrier, and finite parity tests.

All rational certification is via integer arithmetic. Safe under python -O.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import factorial

def demand(on, message):
    if not on:
        raise ValueError(message)

PLO = Q(3141592653589793, 10**15)
PHI = Q(3141592653589794, 10**15)
A5, A8 = Q(29, 40), Q(7, 10)
M = 2048
SCALE = 10**22
END = 32
EPS = Q(1,M)

def arctan_bounds(inv, m):
    total = sum((Q((-1)**j, (2*j+1)*inv**(2*j+1)) for j in range(m)), Q(0))
    following = Q((-1)**m, (2*m+1)*inv**(2*m+1))
    return min(total,total+following),max(total,total+following)

def numerical():
    alo, ahi = arctan_bounds(5, 16)
    blo, bhi = arctan_bounds(239, 8)
    demand(PLO < 16*alo-4*bhi <= 16*ahi-4*blo < PHI, "Machin test for pi")
    log2low = 2*sum((Q(1,(2*j+1)*3**(2*j+1)) for j in range(16)), Q(0))
    rank8_abs_ub = PHI**8 / (14*factorial(8))
    demand(rank8_abs_ub < Q(1681, 10**5), "rank 8")
    # All monomial signs in the integrand polynomial are recorded literally.
    p2lo,p2hi=PLO**2,PHI**2
    w0=2 - A8*p2lo**3/2520
    w1=-A5*p2lo/3
    w2=A8*21*p2hi**2/2520
    w3=A5/3
    w4=-A8*35*p2lo/2520
    w6=A8*7/2520
    # exp(h) >= 1+h+h^2/2: propagate the lower bound rounding down.
    mul_num, mul_den = 2*M*M+2*M+1,2*M*M
    ex_lo=SCALE
    # Round each positive rectangle up for efficient exact summation.
    upper=0
    for i in range(END*M):
        t,u=Q(i,M), Q(i+1,M)
        poly=max(Q(0),w0+w1*t+w2*u*u+w3*u**3+w4*t**4+w6*u**6)
        term=poly*Q(SCALE**2,M*(SCALE+ex_lo))
        upper+=(term.numerator+term.denominator-1)//term.denominator
        ex_lo=ex_lo*mul_num//mul_den
    # Tail: throw away negative monomials, and replace logistic by exp(-t).
    def incfac(k):
        return sum((Q(factorial(k)*END**j,factorial(j)) for j in range(k+1)),Q(0))
    tail=Q(SCALE,ex_lo)*(2+w2*incfac(2)+w3*incfac(3)+w6*incfac(6))
    bill=Q(upper,SCALE)+tail
    demand(bill<Q(836390866608,10**12), "upper integral")
    lower=2*log2low - A8*rank8_abs_ub - bill
    demand(lower>Q(538,1000),f"one-marker lower {float(lower)}")
    demand(Q(200,53)*lower>Q(203,100), "central upper recipe only")
    print(f"rational rectangle upper {float(bill):.12f}; certified lower > .538 (value {float(lower):.12f})")

def angular_fixture():
    tested=0
    for k in range(2,10):
        for subset in combinations(range(1,18),k-1):
            # Strictly increasing actual integer log fixtures in [1,29].
            vals=subset+(29,)
            # Avoid a half divisor: odd total is enough.
            T=sum(vals)
            if not T%2:
                continue
            short=[(len(a),sum(a)) for j in range(k+1) for a in combinations(vals,j) if 2*sum(a)<T]
            F=sum((-1)**len(a)*abs(2*sum(a)-T) for j in range(k+1) for a in combinations(vals,j))
            Z=-4*sum((-1)**j*s for j,s in short)
            A=sum((-1)**j for j,s in short)
            demand(F-Z == (0 if k%2==0 else 2*T*A), "exact full-transfer limit")
            if k==5:
                expected=0 if vals[-1]*2>T else 6-2*sum(2*sum(t)>T for t in combinations(vals,2))
                demand(A==expected, "rank five graph classification")
            tested+=1
            if tested >= 2000*k:
                break
    # Include nongiant balanced and strict 4-star adverse fixtures explicitly.
    for vals, expected in [((18,19,20,21,23),6), ((11,12,13,14,45),-2), ((11,12,13,14,57),0)]:
        T=sum(vals)
        demand(T%2,"rank-five sample")
        A=sum((-1)**j for j in range(6) for t in combinations(vals,j) if 2*sum(t)<T)
        demand(A==expected, "explicit rank-five chamber")
    print(f"{tested} exact parity/half-transfer checks and three rank-five chambers")

if __name__=="__main__":
    numerical()
    angular_fixture()
