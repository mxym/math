#!/usr/bin/env python3
"""Exact finite algebra fixtures only; does not test the analytic estimates."""
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, lcm, prod

def check(ok, data):
    if not ok:
        raise ValueError(data)

def iprime(n):
    return n >= 2 and not any(n % d == 0 for d in range(2, 1 + isqrt(n)))

def factors(n):
    out = {}
    for p in range(2, n + 1):
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        if n == 1:
            break
    return out

def rad(n):
    return prod(factors(n))

def sym(n, mode):
    exps = factors(n)
    if mode == "lambda":
        return (-1) ** sum(exps.values())
    if mode == "one":
        return 1
    mu = 0 if any(e > 1 for e in exps.values()) else (-1) ** len(exps)
    return mu if mode == "mu" else mu * mu

# Logarithmic derivative coefficientwise in the formal variables log p.
logcases = 0
for n in range(2, 901):
    for mode in ("mu", "lambda"):
        for p, exponent in factors(n).items():
            direct = sym(n, mode) * exponent
            split = sum((-1 if mode == "mu" else (-1)**j) * sym(n // p**j, mode)
                        for j in range(1, exponent + 1))
            check(direct == split, ("log", n, mode, p, exponent, direct, split))
            logcases += 1

# Exact additive rational-phase split on the identity X|k, including nonunit XY residues.
phases = splits = 0
for X in range(2, 49):
    for d in range(1, 48):
        d1 = prod(p**e for p, e in factors(d).items() if X % p == 0)
        d0 = d // d1
        check(gcd(d0, d1) == gcd(d0, X) == 1, ("split", X, d, d0, d1))
        for l in range(-8, 9):
            k = X*l
            for a in range(-3, 5):
                lhs = Fraction(a*l, d)
                rhs = Fraction(0)
                if d0 > 1:
                    rhs += Fraction(a*pow(d1, -1, d0)*pow(X, -1, d0)*k, d0)
                if d1 > 1:
                    rhs += Fraction(a*pow(d0, -1, d1)*l, d1)
                check((lhs-rhs).denominator == 1, ("phase", X, d, k, a))
                phases += 1
        for c in range(d0):
            e = gcd(c, d0)
            q = d0//e
            for w in range(1, 2*d0+2):
                v = e*w
                check((v % d0 == c) == (w % q == (c//e) % q and gcd(w,q) == 1),
                      ("nonunit progression", X, d, c, e, v, w, q))
                splits += 1

# Complete joint modular models, not interval or density computations.
# Condition on target units / affine rail, and (optional) bilateral roughness
# on a disjoint fixed set of primes. Tags use two families to audit off-diagonal.
def verify_crt(P, a, b, colors1, colors2, rough):
    banks = [colors1, colors2]
    used = [p for B in banks for c in B for p in c]
    check(len(set(used)) == len(used) and all(iprime(p) for p in used), ("banks", banks))
    check(all(gcd(p,a*b*P) == 1 and p not in rough for p in used), ("units outside banks", P, a,b))
    # Fixed rail, target-unit and rough constraints on small primes.
    M0 = lcm(a*b, rad(P), prod(rough))
    allowed_rail = [x for x in range(M0)
                    if x % a == 0 and x % b == P % b and gcd(x,P) == 1
                    and all(x % p and (P-x) % p for p in rough)]
    expected = Fraction(1,a*b)
    for p in set(factors(P)) | set(rough):
        if p not in rough:
            expected *= Fraction(p-1,p)
        else:
            expected *= Fraction(p-(1 if p in factors(P) else 2),p)
    check(Fraction(len(allowed_rail),M0) == expected, ("rail", P,a,b,rough))
    check(bool(allowed_rail), ("empty rail", P,a,b,rough))
    means = []
    for colors in banks:
        B = [p for block in colors for p in block]
        A = [prod(u) for u in product(*colors)]
        D = prod(Fraction(p-1,p) for p in B)
        U = sum(prod(Fraction(1,p-1) for p in factors(t)) for t in A)
        samples = []
        for r in range(prod(B)):
            triggered = [u for u in A if (P-r) % u == 0]
            avoided = all(r % p for p in B)
            samples.append(Fraction(len(triggered) if avoided else 0,1)/(D*U))
        mu = sum(samples)/len(samples)
        m2 = sum(z*z for z in samples)/len(samples)
        exact2 = sum(prod(Fraction(1,p-1) for p in factors(lcm(u,v))) for u in A for v in A)/(D*U*U)
        check(mu == 1 and m2 == exact2, ("moment", P,a,b,B))
        means.append(mu)
    check(prod(means) == 1, ("mixed", P, a,b))

cases = [
    (32,1,1,[[5,7],[11]],[[13,17],[19]],[2,3]),
    (128,3,5,[[7,11],[13]],[[17,19],[23]],[2]),
    (324,5,7,[[11,13],[17]],[[19,23],[29]],[2,3]),
    (200,3,7,[[11,13],[17]],[[19,23],[29]],[2,5]),
]
for c in cases:
    verify_crt(*c)

# Sign-factor reduction in the literal target gcd strata and squarefree pairs.
gcdcases = squarecases = 0
for N in range(3, 190):
    for x in range(1, N):
        d = gcd(x,N)
        P,m,n = N//d, x//d, (N-x)//d
        check(gcd(m,P) == gcd(n,P) == 1, ("partition", N,x,d))
        for mode in ("mu","lambda","mu_sq","one"):
            for y,z in ((x,m),(N-x,n)):
                retained = (mode in ("lambda","one") or gcd(z,d) == 1)
                check(sym(y,mode) == sym(d,mode)*sym(z,mode)*retained,
                      ("factor masks", N,x,d,mode,y,z,retained))
                gcdcases += 1
    for p in (2,3,5,7,11):
        count = sum((r % (p*p) != 0 and (N-r) % (p*p) != 0) for r in range(p*p))
        check(count == p*p-2+(N % (p*p) == 0), ("quadratic residue mask",N,p))
        squarecases += 1
print("PASS exact logarithmic coefficients",logcases,"phases",phases,
      "nonunit residue divisions",splits,"CRT moment fixtures",len(cases),
      "gcd-stratum coefficients",gcdcases,"squarefree local factors",squarecases)
