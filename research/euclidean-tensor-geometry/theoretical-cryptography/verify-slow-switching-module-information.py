#!/usr/bin/env python3
"""Exact finite checks for slow-switching-module-information.md."""

from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import factorial, comb, prod


def overlapping_bayes():
    states = (0, 1)
    xs = tuple(product((0, 1), repeat=2))
    outcomes = tuple(product(xs, states))
    wgt = {}
    for s in states:
        den = sum((i+1 if not s else 8-i) for i in range(8))
        wgt[s] = {xy: Q(i+1 if not s else 8-i, den)
                  for i, xy in enumerate(outcomes)}
    counts = 0
    for m in (1, 2, 3):
        words = tuple(product(states,repeat=m))
        source = {}
        for w in words:
            prior = Q(1,2) * prod(
                Q(2,3) if w[i]==w[i-1] else Q(1,3) for i in range(1,m)
            )
            for samples in product(outcomes,repeat=m):
                x,y = zip(*samples)
                p = prior * prod(wgt[s][obs] for s,obs in zip(w,samples))
                source[w,x,y] = p
        assert sum(source.values()) == 1
        for quotient in ((0,), (1,), (0,1)):
            yu, wyu, wy, yv = [defaultdict(Q) for k in range(4)]
            for (w,x,y),p in source.items():
                u = tuple(tuple(v[i] for i in quotient) for v in x)
                yu[y,u] += p
                wyu[w,y,u] += p
                wy[w,y] += p
                yv[y] += p
            for (w,y,u),p in wyu.items():
                iu_given_w = p/wy[w,y]
                iu = yu[y,u]/yv[y]
                w_given_u = p/yu[y,u]
                w_given_y = wy[w,y]/yv[y]
                assert iu_given_w/iu == w_given_u/w_given_y
                counts += 1
    return counts


def compositions(j,k):
    if not k:
        if j == 0:
            yield ()
    else:
        for a in range(j+1):
            for rest in compositions(j-a,k-1):
                yield (a,) + rest


def occupation_moments():
    checks = 0
    for K,start in product(range(10),(0,1)):
        durations = K+1
        a = sum((start+j)%2 for j in range(durations))
        b = durations-a
        if K:
            assert a>0 and b>0
        for j in range(8):
            exact_simplex = sum(
                (Q(factorial(j),prod(factorial(x) for x in c)) *
                 Q(factorial(K)*prod(factorial(x) for x in c),factorial(K+j))
                 for c in compositions(j,a)), Q()
            )
            beta_moment = Q(prod(a+i for i in range(j)),
                            prod(a+b+i for i in range(j)))
            assert exact_simplex == beta_moment
            if a>0 and j:
                assert len(list(compositions(j,a))) == comb(a+j-1,j)
            checks += 1
    return checks


def two_state_covariance():
    count = 0
    for alpha,beta,difference in product(map(Q, ("1","2/3","3/2","4")), repeat=3):
        stat = (beta/(alpha+beta),alpha/(alpha+beta))
        h = (Q(0),difference)
        mean = sum(p*x for p,x in zip(stat,h))
        f = tuple(x-mean for x in h)
        g = tuple(x/(alpha+beta) for x in f)
        assert alpha*(g[0]-g[1]) == f[0]
        assert beta*(g[1]-g[0]) == f[1]
        var = (stat[0]*alpha+stat[1]*beta)*(g[1]-g[0])**2
        assert var == 2*alpha*beta*difference**2/(alpha+beta)**3
        if alpha==beta:
            assert var == difference**2/(4*alpha)
        count += 1
    return count


if __name__ == "__main__":
    b = overlapping_bayes()
    o = occupation_moments()
    c = two_state_covariance()
    print(f"PASS: {b} exact posterior-ratio equations with overlapping emissions")
    print(f"PASS: {o} occupation simplex/Beta moments and {c} Poisson-equation cases")
