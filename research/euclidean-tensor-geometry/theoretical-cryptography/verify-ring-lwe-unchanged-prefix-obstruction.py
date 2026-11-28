#!/usr/bin/env python3
"""Exact finite arithmetic checks for the unchanged-prefix obstruction."""
from fractions import Fraction as F
from itertools import product
from math import ceil, floor


def simplex(n,d):
    if d==1:
        yield (F(1),)
        return
    def counts(s,k):
        if k==1:
            yield (s,)
        else:
            for x in range(s+1):
                for rest in counts(s-x,k-1):
                    yield (x,)+rest
    for xs in counts(n,d):
        yield tuple(F(x,n) for x in xs)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def overlap(prior, emission, k):
    q = len(prior)
    mixture = [sum(prior[j]*emission[j][i] for j in range(q))
               for i in range(len(k))]
    tv = sum(prior[j]*sum(abs(emission[j][i]-k[i])
                         for i in range(len(k)))/2 for j in range(q))
    ol = sum(mixture[i]*sum(prior[j]*min(emission[j][i]/mixture[i],
                                       k[i]/mixture[i])
                            for j in range(q)) for i in range(len(k)))
    assert 1-ol == tv
    return ol


def overlap_checks():
    rows = 0
    for f in [(F(1,2),F(1,3),F(1,6)),
              (F(4,5),F(1,10),F(1,10)),
              (F(1,11),F(7,11),F(3,11))]:
        emission = [[f[(y-j)%3] for y in range(3)] for j in range(3)]
        for p in list(simplex(8,3))+[(F(1,3),)*3]:
            pred = [sum(p[j]*emission[j][y] for j in range(3))
                    for y in range(3)]
            pred_ol = overlap(p,emission,pred)
            for k in simplex(7,3):
                ol = overlap(p,emission,k)
                if p==(F(1,3),)*3:
                    assert ol <= pred_ol
                rows += 1
    # Predictive optimality is not claimed in a finite experiment.
    ps = (F(3,4),F(1,4))
    a,b = (F(2,3),F(1,3)),(F(1,3),F(2,3))
    predictive = tuple(ps[0]*x+ps[1]*y for x,y in zip(a,b))
    assert overlap(ps,(a,b),a) > overlap(ps,(a,b),predictive)
    return rows


def posterior_covariances():
    # Four exact phases; this checks trace and the angular factor 1/2.
    vs = ((1,0),(0,1),(-1,0),(0,-1))
    rows = 0
    for p in simplex(10,4):
        mx,my = [sum(pj*v[i] for pj,v in zip(p,vs)) for i in range(2)]
        mu = (mx,my)
        radial = 1-dot(mu,mu)
        assert radial == sum(p[i]*p[j]*(1-dot(vs[i],vs[j]))
                             for i,j in product(range(4),repeat=2))
        variances = [sum(pj*dot(v,h)**2 for pj,v in zip(p,vs))-dot(mu,h)**2 for h in vs]
        assert sum(variances)/4 == radial/2
        rows += 1
    return rows


def likelihood_square():
    rows = 0
    for p in simplex(8,3):
        first = (F(1,3),F(2,3),F(3,4))
        second = first[::-1]
        for a,b in ((first,second),(second,first)):
            x = tuple(v/dot(p,a) for v in a)
            y = tuple(v/dot(p,b) for v in b)
            assert dot(p,x)==dot(p,y)==1
            assert sum(p[i]*p[j]*(x[i]*y[j])**2 for i,j in
                       product(range(3),repeat=2)) == (
                       1+sum(p[i]*(x[i]-1)**2 for i in range(3)))*(
                       1+sum(p[i]*(y[i]-1)**2 for i in range(3)))
            rows += 1
    return rows


def projection():
    rows = 0
    for d,n,k,g in product(range(3,18),range(1,10),
                           range(1,8),range(1,5)):
        a2,g = F(n,4*k*d),F(g,2)
        r = ceil(4*g/(d*a2))
        rp = ceil(2*g/(d*a2))
        dp = floor(g/(rp*a2))
        assert rp<=r and 2*dp<=d
        assert 0<=g-dp*rp*a2<rp*a2
        rows += 1
    return rows


if __name__ == "__main__":
    print("PASS Bayes-overlap laws:", overlap_checks())
    print("PASS posterior covariance / second-moment rows:",
          posterior_covariances(),likelihood_square())
    print("PASS projection scale rows:",projection())
