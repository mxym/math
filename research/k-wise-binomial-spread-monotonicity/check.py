"""Finite exact corroboration by exhaustive paired-basis enumeration (standard library)."""
from fractions import Fraction
from itertools import combinations
from math import comb, prod, isqrt
from functools import lru_cache

def require(value):
    if not value:
        raise ArithmeticError("finite certificate failed")

def poly_trim(u):
    while u and u[-1] == 0:
        u.pop()
    return u

def gcd(u, v):
    a=poly_trim(list(map(Fraction,u))); b=poly_trim(list(map(Fraction,v)))
    while b:
        while len(a)>=len(b):
            h=a[-1]/b[-1]; offset=len(a)-len(b)
            for j,v in enumerate(b): a[j+offset]-=h*v
            poly_trim(a)
        a,b=b,a
    return tuple(a)

def eval_odds(coeff,p):  # homogeneous value at z=p/(1-p), valid also at the endpoints
    t,d=p.numerator,p.denominator
    return sum(c*t**x*(d-t)**(len(coeff)-1-x) for x,c in enumerate(coeff))

@lru_cache(maxsize=8192)
def powers(N,p):
    t,d=p.numerator,p.denominator
    return tuple(t**x*(d-t)**(N-x) for x in range(N+1))

def feasible(N,J):
    # A lower threshold must be exceeded; an upper threshold must not be reached.
    # Its expression is the signed numerator of E_G[X]-s, with strictly
    # increasing tilted mean E_G[X] on the interior (at least two possible sites).
    lower=[]; upper=[]
    for a in J:
        coeff=[comb(N,x)*prod((x-b)*(x-b-1) for b in J if b!=a) for x in range(N+1)]
        lower.append(tuple((x-a)*v for x,v in enumerate(coeff)))
        upper.append(tuple((x-a-1)*v for x,v in enumerate(coeff)))
    l=Fraction(0); h=Fraction(1)
    for _ in range(60):
        t=(l+h)/2; w=powers(N,t)
        low=all(sum(c*v for c,v in zip(row,w))>0 for row in lower)
        high=all(sum(c*v for c,v in zip(row,w))<0 for row in upper)
        if low and high:return True
        if not (low or high):return False
        if not low:l=t
        else:h=t
    # Unresolved dyadic comparisons are not rounded to ties: certify a
    # common positive real root of a lower and an upper threshold in the bracket.
    for a in lower:
        for b in upper:
            g=gcd(a,b)
            if len(g)>=2 and eval_odds(g,l)*eval_odds(g,h)<0:return False
    raise ArithmeticError("unresolved possible phase")

alltests=0; allphases=0
for k in (2,4,6,8,10,12):
    vals=[]
    for n in range(k+1,17):
        N=n-1; candidates=0; spreads=[]
        for J in combinations(range(N),k//2):
            if any(a+1>=b for a,b in zip(J,J[1:])):continue
            candidates+=1
            if feasible(N,J):spreads.append(J[-1]+1-J[0])
        require(candidates==comb(n-k//2,k//2))
        require(min(spreads)==k-1)
        largest=max(spreads); vals.append(largest)
        if k==4 and n>=6:require(largest==isqrt(n-2)+2)
        alltests+=candidates; allphases+=len(spreads)
    require(all(a<=b for a,b in zip(vals,vals[1:])))
    print(f"k={k}, n={k+1}..16, exact maxima: {vals}")
print("Paired bases exhaustively tested:",alltests,"; positive-length occurrences:",allphases)
print("PASS (finite corroboration; the general result has an analytic proof).")
