#!/usr/bin/env python3
"""Independent finite checks for the high-fitness Moran extremum."""
from fractions import Fraction as F
from itertools import combinations


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def from_edges(n,E):
    G = [set() for _ in range(n)]
    for i,j in E:
        G[i].add(j)
        G[j].add(i)
    return G


def graphs(n):
    pairs = list(combinations(range(n),2))
    for mask in range(1 << len(pairs)):
        E = [edge for i,edge in enumerate(pairs) if mask>>i&1]
        if len(E) < n-1:
            continue
        G = from_edges(n,E)
        reached = {0}
        while True:
            S = reached.union(*(G[i] for i in reached))
            if S == reached:
                break
            reached = S
        if len(reached) == n:
            yield G


def cut(G,S,w):
    up, down = {}, {}
    for u in S:
        for v in G[u] - S:
            up[v] = up.get(v,0) + w[u]
            down[u] = down.get(u,0) + w[v]
    return up, down


def coeff(G):
    n = len(G)
    w = [F(1,len(A)) for A in G]
    # First compute the leading singleton and pair coefficients by the
    # downward branch of the exact cut equation, not the edge formula.
    t = [sum(w[v] for v in A) for A in G]
    require(sum(t) == n, "temperature mass")
    b2 = []
    for u,A in enumerate(G):
        x = -t[u]**2
        for v in A:
            up,down = cut(G,{u,v},w)
            pair = (down.get(u,0)*t[v]+down.get(v,0)*t[u])/sum(up.values())
            x += w[u]*pair
        b2.append(x)
    return sum(b2)/n


def exact_extinction(G, r):
    n = len(G)
    last = (1<<n)-1
    M = [[F(0)]*last for _ in range(last-1)]
    w = [F(1,len(A)) for A in G]
    z = F(1,r)
    for mask in range(1,last):
        row = M[mask-1]
        S = {i for i in range(n) if mask>>i&1}
        up,down = cut(G,S,w)
        row[mask-1] = sum(up.values()) + z*sum(down.values())
        for v,x in up.items():
            new = mask|(1<<v)
            if new != last:
                row[new-1] -= x
        for u,x in down.items():
            new = mask^(1<<u)
            if new:
                row[new-1] -= z*x
            else:
                row[-1] += z*x
    for j in range(last-1):
        k = next(i for i in range(j,last-1) if M[i][j])
        M[j],M[k] = M[k],M[j]
        pivot = M[j][j]
        M[j] = [x/pivot for x in M[j]]
        for i in range(j+1,last-1):
            f = M[i][j]
            if f:
                M[i] = [a-f*b for a,b in zip(M[i],M[j])]
    sol = [F(0)]*(last-1)
    for j in range(last-2,-1,-1):
        sol[j] = M[j][-1] - sum(M[j][i]*sol[i] for i in range(j+1,last-1))
    return sum(sol[(1<<i)-1] for i in range(n))/n


def check():
    record = {3:(4,F(1,2),1),4:(38,F(269,252),12),
              5:(728,F(851,600),30),6:(26704,F(2139,1300),60)}
    exact_cases = 0
    for n,(exp,gap_exp,mult) in record.items():
        k = n-1
        count = stars = tied = 0
        best = None
        astar = (n-k*k-F(1,k))/n
        for G in graphs(n):
            a = coeff(G)
            count += 1
            if n <= 4:
                for r in (2*k,384*k):
                    p = exact_extinction(G,r)
                    z = F(1,r)
                    require(abs(p-z-a*z*z) <= 3*k**3*z**3, ("bad finite remainder",n,r,G))
                    exact_cases += 1
            if sum(len(A)==1 for A in G) == k:
                stars += 1
                require(a==astar,"wrong star coefficient")
                continue
            d = a-astar
            if best is None or d < best:
                best, tied = d, 1
            elif d == best:
                tied += 1
        require((count,best,tied,stars)==(exp,gap_exp,mult,n), ("finite census",n))
        require(best >= F(1,2), "small gap")
        print(n, count, str(best), tied)
    print("PASS:", exact_cases, "separate exact absorption checks")


if __name__ == "__main__":
    check()
