#!/usr/bin/env python3
"""Exact finite first-active and nonunit rectangle fixtures (not analytic bounds)."""
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod

def verify(condition, detail):
    if not condition:
        raise ValueError(detail)

def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]

def phi(n):
    return sum(gcd(t,n)==1 for t in range(1,n+1))

def mu(n):
    result = 1
    p = 2
    while p*p <= n:
        if n%p == 0:
            n //= p
            if n%p == 0:
                return 0
            result = -result
        p += 1
    return -result if n > 1 else result

def active(source, reflected, bank):
    return all(source % p for B in bank for p in B) and all(any(reflected % p == 0 for p in B) for B in bank)

def compare_bank_model(P, a, b, target_primes, banks):
    primes = list(target_primes) + [q for bank in banks for color in bank for q in color]
    Q = lcm(a*b,prod(primes))
    eligible = [x for x in range(Q) if x%a == 0 and (P-x)%b == 0 and gcd(x,P)==1]
    check = Fraction(1)
    for bank in banks:
        D = prod(Fraction(p-1,p) for C in bank for p in C)
        H = prod(1-prod(Fraction(p-2,p-1) for p in C) for C in bank)
        check *= 1-D*H
    missing = sum(not any(active(x,P-x,bank) for bank in banks) for x in eligible)
    verify(bool(eligible) and Fraction(missing,len(eligible)) == check,
           ("no-active CRT",P,a,b,missing,len(eligible),check))
    return len(eligible)

crt = sum(compare_bank_model(*case) for case in [
    (64,1,1,[2],[[[3],[5]],[[7],[11]]]),
    (81,1,1,[3],[[[2],[5]],[[7],[11]]]),
    (256,3,1,[2],[[[5],[7]],[[11],[13]]]),
    (81,1,1,[3],[[[2,5],[7]],[[11],[13]]]),
])

fund = 0
banks = [[[3,5],[7,11]], [[13],[17,19]], [[23,29],[31]]]
for P in range(401,1558):
    if gcd(P,prod(p for bank in banks for color in bank for p in color)) > 1:
        continue
    for source in range(P//3, P//3+37):
        y = P-source
        U = [active(source,y,B) for B in banks]
        literal = int(any(U))
        expansion = sum(int(U[j])*sum((-1)**sum(selected)*prod(int(U[i]) for i in range(j) if selected[i])
                                      for selected in product((0,1), repeat=j))
                        for j in range(len(U)))
        verify(literal == expansion, ("first active",P,source,U))
        for j,B in enumerate(banks):
            if any(y%(p*p)==0 for C in B for p in C):
                continue
            tags = [prod(args) for args in product(*B)]
            accepted = sum(Fraction(1,prod(1+sum((y//u)%r==0 for r in C) for C in B))
                           for u in tags if y%u==0)
            accepted *= all(source%p for C in B for p in C)
            verify(accepted == int(U[j]), ("residual reciprocal",P,source,j,accepted,U[j]))
            for u in tags:
                if y%u==0:
                    for i,A in enumerate(banks):
                        if i!=j:
                            verify(active(source,y,A)==active(source,y//u,A),
                                   ("other bank residual",P,source,u,i,j))
            fund += 1

strata = avg = 0
H = 18
for N in range(3,182):
    ds = divisors(N)
    F = {d:phi(d) for d in ds}
    for a in range(1,H+1):
        for b in range(1,H+1):
            expected = sum(Fraction(phi(r)*phi(s),lcm(r,s))
                           for r in divisors(a) for s in divisors(b) if N%lcm(r,s)==0)
            direct = Fraction(sum(F[N//d]*gcd(a,d)*gcd(b,d) for d in ds), N)
            verify(direct == expected, ("totient average",N,a,b,direct,expected))
            avg += 1
            for m in range(1,(N-1)//a+1):
                x = a*m
                if (N-x)%b:
                    continue
                n=(N-x)//b
                d=gcd(x,N)
                P=N//d
                t=x//d
                ap,bp=a//gcd(a,d),b//gcd(b,d)
                ea,eb=d//gcd(a,d),d//gcd(b,d)
                verify(t%ap==0 and (P-t)%bp==0 and gcd(ap*bp,P)==gcd(ap,bp)==1,
                       ("stratum divisibilities",N,a,b,m,n,d,ap,bp))
                mp,np=t//ap,(P-t)//bp
                verify((m,n)==(ea*mp,eb*np),("stratum back map",N,a,b,m,n,d))
                product_decomposed=(mu(ea)*mu(eb)*mu(mp)*mu(np)*(gcd(ea,mp)==1)*(gcd(eb,np)==1))
                verify(mu(m)*mu(n)==product_decomposed,("stratum Mobius",N,a,b,m,n,d))
                strata += 1
print("PASS exact CRT-eligible residues",crt,"marked reciprocal fixtures",fund,
      "totient averages",avg,"nonunit affine row reductions",strata)
