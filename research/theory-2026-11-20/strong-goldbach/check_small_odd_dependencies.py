"""Finite exact checks; no assertions, packages, or asymptotic threshold assumptions."""
from itertools import combinations
from math import gcd, isqrt, prod


def check(ok, tag):
    if not ok:
        raise ValueError(tag)


def factors(n):
    d, ans = 2, {}
    while d*d <= n:
        while n % d == 0:
            ans[d] = ans.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        ans[n] = 1
    return ans


def pair_ledger():
    cnt = 0
    prim = [p for p in range(3, 42, 2) if factors(p) == {p: 1}]
    for N in range(6, 3001, 2):
        X = [p for p in prim if p < N-1 and N % p]
        odds = {p: {q for q, e in factors(N-p).items() if e % 2} for p in X}
        pairs = []
        for p,q in combinations(X, 2):
            parity = (odds[p] ^ odds[q]) == {p,q}
            U2, rem = divmod((N-p)*(N-q), p*q)
            U = isqrt(U2)
            check(parity == (rem == 0 and U*U == U2), ("full width",N,p,q))
            if not parity:
                continue
            cnt += 1
            pairs.append({p,q})
            check(q in odds[p] and p in odds[q], "mutual")
            check(U*U % N == 1, "signed square")
            D = [1,1]
            for r, e in factors(N).items():
                P = r**(e-int(r == 2))
                if (U-1) % P == 0:
                    D[0] *= P
                else:
                    check((U+1) % P == 0, ("local signs",N,p,q,r))
                    D[1] *= P
            check(prod(D)*2 == N and gcd(*D) == 1, "coprime split")
            for m,sgn in zip(D,(1,-1)):
                J,rem=divmod(U-sgn,m)
                E=N//m
                check(rem == 0 and 0 < abs(p*q*J*J-E*E)*N <= 8*(p+q)*E*E,
                      ("integer approximation",N,p,q,m))
        check(not any(a & b for a,b in combinations(pairs,2)), "shared-pair impossibility")
    check(cnt > 0 and (852-5)*(852-7) == 5*7*143**2, "852")
    print("two-label full-width words", cnt)


def pell():
    u=v=1
    for n in range(7):
        N=3+7*u*u
        check(N==7+3*v*v and N%4==2 and gcd(N,21)==1, "Pell closure")
        if n==1:
            check((u,v,N)==(91,139,57970),"first non-endpoint")
        u, v = 55*u+36*v, 84*u+55*v
    print("Pell controls", 7)


def menus():
    N=10*17**4
    bits=lambda x: (int(x%4==3),int(pow(x,2,5)==4))
    check(bits(11)==(1,0) and bits(13)==(0,1) and bits(N-1)==(0,0),"character rank")
    check(factors(N-11)=={23:1,36313:1} and factors(N-13)=={3:1,11:1,25309:1},
          "two physical disjoint escapes beyond 31")
    print("rank-two fixture", N)


if __name__=="__main__":
    pair_ledger()
    pell()
    menus()
