"""Exact finite examples for both deterministic lemmas, the frontier, and attainment."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import comb, prod


def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)


def pointwise():
    count = 0
    for n in range(2, 7):
        # Scaled by eight, including both exact thresholds.
        for x in combinations_with_replacement(range(9), n):
            s = sum(x)
            f = max(8-s, 0)
            fi = [max(8-s+t, 0) for t in x]
            require(8*f**(n-1) <= prod(fi), ("projection product", x))
            require(sum(g-f for g in fi) <= 8*(s<16)-f, ("deletions", x))
            require(max(16-s, 0) <= 8*(s<16)+f, ("shortage", x))
            count += 1
    return count


def frontier(rows):
    n=len(rows); c=[1]; denom=1
    for row in rows:
        new = [0]*(len(c)+4)
        for i,b in enumerate(c):
            for j,d in enumerate(row):
                new[i+j] += b*d
        c=new; denom*=sum(row)
    require(sum(c)==denom, "mass")
    q=F(sum(c[:8]),denom)
    a=F(sum((4-i)*v for i,v in enumerate(c[:4])),4*denom)
    h=F(sum((8-i)*v for i,v in enumerate(c[:8])),4*denom)
    require(((q+(n-1)*a)/n)**n>=a**(n-1), ("finite lower bound for q",rows))
    require(h<=q+a, ("shortage upper bound",rows))
    return q,a,h


def main():
    print("Sorted eighth-grid deterministic profiles:", pointwise())
    # Non-symmetric, degenerate, endpoint, and mixed fractional marginal laws.
    laws=[(1,0,0,0,0),(0,0,0,0,1),(0,0,1,0,0),(1,0,0,0,2),
          (2,3,0,1,0),(0,1,0,3,1),(1,1,1,1,1)]
    tries=0
    for n in range(2, 7):
        for rows in combinations_with_replacement(laws, n):
            frontier(rows); tries+=1
    print("Independent product laws on the quarter-grid:",tries)
    tries=0
    for n in range(2,16):
        for num in range(12):
            z=F(num,11)
            q,a,h=frontier([(num,0,0,0,11-num)]*n)
            require(a==z**n and q==n*z**(n-1)-(n-1)*z**n and h==q+a,"equality")
            tries+=1
    print("Exact binomial equality cases (including endpoints):",tries)
    print("PASS; finite checks supplement, not replace, the all-law proof.")


if __name__=="__main__":
    main()
