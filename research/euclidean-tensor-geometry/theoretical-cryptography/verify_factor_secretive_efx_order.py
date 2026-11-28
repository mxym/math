#!/usr/bin/env python3
"""Finite exact checks for secretive EFX: no external dependencies."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from random import Random


def require(ok, msg):
    if not ok:
        raise AssertionError(msg)


def residual(v, B):
    # Compute by deleting each individual good, not by the greedy update rule.
    return max((sum(v[g] for g in P if g != h) for P in B for h in P), default=0)


def eligible(V, B, alpha):
    return [{j for j,P in enumerate(B) if sum(v[g] for g in P) >= a*residual(v,B)}
            for v,a in zip(V,alpha)]


def robust(E, n):
    # Given a concrete threshold graph, test actual matchings after deletion.
    for rest in combinations(range(n),len(E)):
        if not any(all(j in row for row,j in zip(E,p)) for p in permutations(rest)):
            return False
    return True


def construct(V, alpha, order):
    n = len(V)+1
    m = len(order)
    B = [[] for _ in range(n)]
    X = [[1+int(i==j) for j in range(n)] for i in range(n-1)]
    for u,g in enumerate(order):
        totals = [[sum(v[h] for h in P) for P in B] for v in V]
        E = eligible(V, B, alpha)
        used = [sum(row[j] for row in X) for j in range(n)]
        require(sorted(used)==[n-1]+[n]*(n-1),"bad column capacities")
        j = used.index(n-1)

        def shifting(j):
            for i,row in enumerate(X):
                if j in E[i]:
                    for b,x in enumerate(row):
                        if x and totals[i][b]<totals[i][j]:
                            return i,b
            return None

        count = 0
        while True:
            step = shifting(j)
            if step is None:
                break
            i,b = step
            X[i][b] -= 1
            X[i][j] += 1
            j = b
            count += 1
            require(count <= (n*n-1)*(n-1),"rank potential")
        B[j].append(g)
        E = eligible(V, B, alpha)
        require(all(not x or t in E[i] for i,row in enumerate(X) for t,x in enumerate(row)),
                "a positive support edge stopped being eligible")
    require(sorted(g for P in B for g in P)==list(range(m)),"not a partition")
    require(robust(eligible(V,B,alpha),n),"no deletion-robust matching")
    return B


def fit_order(V, f):
    m = len(V[0])
    edges = [{b for b in range(m) if b != h and any(v[b] < a*v[h] for v,a in zip(V,f))}
             for h in range(m)]
    avail = set(range(m))
    order = []
    while avail:
        unblocked = avail.difference(set().union(*(edges[i] for i in avail)))
        if not unblocked:
            return None
        h = min(unblocked)
        avail.remove(h)
        order.append(h)
    return order


def optimal(V):
    try_factors = {F(0),F(1)}
    for v in V:
        for a,b in permutations(v,2):
            if b and a<=b:
                try_factors.add(F(a,b))
    for a in sorted(try_factors,reverse=True):
        P = fit_order(V,[a]*len(V))
        if P is not None:
            return a,P
    raise AssertionError("zero should be feasible")


def direct_best(V):
    m = len(V[0])
    return max(min((F(v[a],v[b]) for v in V for i,a in enumerate(p)
                   for b in p[i+1:] if v[b]),default=F(1))
               for p in permutations(range(m))) if m>=2 else F(1)


def small_goods(V,n):
    m = len(V[0])
    if m<=n:
        return [(j,) if j<m else () for j in range(n)]
    if m==n+1:
        return [(j,) for j in range(n-1)] + [(n-1,n)]
    P = [(j,) for j in range(n-2)] + [(n-2,n+1),(n-1,n)]
    if any(v[n-1]+v[n]>=v[n-2] for v in V):
        return P
    return [(j,) for j in range(n-1)] + [(n-1,n,n+1)]


def adversary():
    V = [[10,9,8,7,6,5,4],[14,13,5,4,3,2,1]]
    count = 0
    for p in product(range(4), repeat=7):
        B = [[g for g,j in enumerate(p) if a==j] for a in range(4)]
        require(not robust(eligible(V,B,[1,1]),4),("two-deletion counterexample failed",p))
        count += 1
    require(count==4**7,"missing a labeled partition")
    return count


def main():
    R = Random(160861)
    count_exact = count_approx = short = 0
    for n in range(2,8):
        for q in range(60):
            m = R.randrange(0,16)
            V = [sorted([R.randrange(0,17) for _ in range(m)],reverse=True)
                 for _ in range(n-1)]
            construct(V,[1]*(n-1),list(range(m)))
            count_exact += 1
            if m <= n+2:
                W = V[:R.randrange(1,n)]
                require(robust(eligible(W,small_goods(W,n),[1]*len(W)),n),"n+2 construction")
                short += 1
            V = [[R.randrange(0,14) for _ in range(m%6)] for _ in range(n-1)]
            a,order = optimal(V)
            # Clamp to [0,1], including the case without any positive denominator.
            require(min(F(1),direct_best(V)) == a, ("wrong best common ratio",V,a))
            construct(V,[a]*(n-1),order)
            count_approx += 1
    cyclic = [[4,3,2],[2,4,3],[3,2,4]]
    require(optimal(cyclic)[0]==F(1,2),"strict three-cycle threshold")
    print("PASS",count_exact,count_approx,short,adversary())


if __name__ == "__main__":
    main()
