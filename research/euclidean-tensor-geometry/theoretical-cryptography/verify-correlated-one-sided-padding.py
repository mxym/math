#!/usr/bin/env python3
"""Reproduce finite identities used in the correlated one-sided padding proof."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, exp, factorial, fsum


def sum_t(vertices, matrix):
    return sum(matrix[i][j] for i in vertices for j in vertices)


def masks():
    tests = 0
    for d in range(2,10):
        V = [[(11*i*j+3*i+7*j+5)%17-8 for i in range(d)] for j in range(4)]
        J = [[sum(row[i]*row[j] for row in V) for j in range(d)] for i in range(d)]
        tr = sum(J[i][i] for i in range(d))
        ones = sum(map(sum,J))
        for k in range(d+1):
            have = F(sum(sum_t(s,J) for s in combinations(range(d),k)),comb(d,k))
            want = F(k*(d-k),d*(d-1))*tr+F(k*(k-1),d*(d-1))*ones
            assert have==want
            lower = F(k*(d-k),d-1)+F(k*(k-1),d*(d-1))
            assert lower==F(k*(d+1-k),d)
            a = F(k,d)
            w2 = k*(1-a)**2+(d-k)*a*a
            assert w2==F(k*(d-k),d) and w2<=F(d,4)
            tests += 3
        assert max(k*(d+1-k) for k in range(d+1))==(d+1)**2//4
    return tests


def shifts():
    count=0
    for n in range(1,8):
        for vec in product((-1,0,2),repeat=n):
            g=list(vec)+[0]
            S=[F(x+y,2) for x,y in zip(g,g[1:])]
            D=sum((y-x)**2 for x,y in zip(g,g[1:]))
            norm=sum(x*x for x in g)
            assert sum(x*x for x in S)==norm - F(g[0]**2,2)-F(D,4)
            for N in range(1,n+1):
                assert sum(x*x for x in g[:N])<=N*N*(D+g[0]**2)
                count+=1
    return count


def overlap_tensor():
    count=0
    for d in range(2,5):
        for salt in range(10):
            f={j: ((sum((i+1)*x for i,x in enumerate(j))+salt)**2+1)%19
               for j in product(range(4),repeat=d)}
            def pair(mask):
                return sum(a*f.get(tuple(x+y for x,y in zip(j,mask)),0)
                           for j,a in f.items())
            all_bits=tuple(product((0,1),repeat=d))
            direct=F(sum(map(pair,all_bits)),2**d)
            S=f
            for i in range(d):
                S={j:F(a+S.get(j[:i]+(j[i]+1,)+j[i+1:],0),2)
                   for j,a in S.items()}
            assert direct==sum(a*S[j] for j,a in f.items())
            count+=1
    return count


def simpson(fun,a,b,n=10000):
    dx=(b-a)/n
    return dx/3*(fun(a)+fun(b)+4*fsum(fun(a+i*dx) for i in range(1,n,2))
                  +2*fsum(fun(a+i*dx) for i in range(2,n,2)))


def trimmed_ratios():
    n=0
    max_rel=0.0
    # Gamma(L+1,L+1) has mean 1 and Fisher (L+1)^2/(L-1).
    # Higher vanishing orders permit both signs on the trimmed domain.
    for L,b,sign in product((4,6,10,14),(.65,1.0),(-1,1)):
        rate=(L+1)/b
        I=rate*rate/(L-1)
        c=rate**(L+1)/factorial(L)
        h=.003
        for t in (sign*h, sign*h/4):
            def integrand(x):
                if x==0:
                    return 0.0
                return c*x**L*(x/(x+t))**L*exp(-rate*(x-t))
            val=simpson(integrand,2*h,18)
            rel=abs((val-1)/(I*t*t)-1)
            max_rel=max(rel,max_rel)
            assert rel < .04
            n+=1
            if sign>0:
                pos=simpson(integrand,0,18)
                assert (pos-1)/(I*t*t) < exp(rate*t) + 1e-8
    return n,round(max_rel,6)


def main():
    print("PASS exact mask and mean-subtraction identities:",masks())
    print("PASS unilateral averaging norm/telescoping identities:",shifts())
    print("PASS exact product overlap operators:",overlap_tensor())
    print("PASS scalar toy trimmed integrals (cases, max relative error):",trimmed_ratios())


if __name__=="__main__":
    main()
