"""Exact arithmetic checks. Run with Python 3 and assertions enabled."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product, permutations
from random import Random


def raw(mass, W, den=1):
    """p and F: integrate out x in x-y-u-v first via weighted codegrees."""
    n, D = len(mass), sum(mass)
    d = [sum(m * a for m, a in zip(mass, r)) for r in W]
    e = sum(m * a for m, a in zip(mass, d))
    # Expand P4 minus C4 in units D^4 * den^4.
    path = sum(mass[i]*mass[j]*W[i][j]*d[i]*d[j]
               for i, j in product(range(n), repeat=2))
    cyc = sum(mass[i]*mass[j]*sum(m*a*b for m, a, b in
                  zip(mass, W[i], W[j]))**2 for i, j in product(range(n), repeat=2))
    return Q(e, D**2*den), Q(den*path-cyc, D**4*den**4)


def four(m, W, den):
    """Brute-force conditional failures, separately for each same first-class pair."""
    n, D = len(m), sum(m)
    p, F = raw(m, W, den)
    if not p:
        return
    ordered = fail = 0
    rowfail = [0]*n
    for x, y, u, v in product(range(n), repeat=4):
        e = m[x]*m[y]*m[u]*m[v]*W[x][y]*W[u][v]
        a, b = W[y][u], W[v][x]
        ordered += e*a*(den-b)
        h = e*(a*b+(den-a)*(den-b))
        fail += h
        if x == u:
            rowfail[x] += h
    norm = (D*den)**4
    assert Q(ordered,norm) == F
    assert Q(fail,norm)/(2*p**2) == Q(1,2)-F/p**2
    pi = []
    for i, row in enumerate(W):
        d = sum(z*a for z,a in zip(m,row))
        if not d:
            continue
        a = Q(m[i]*d,D*D*den)/p
        t = Q(sum(z*w*w for z,w in zip(m,row)),d*den)
        assert Q(rowfail[i],norm)/p**2 == a*a*(t*t+(1-t)**2)
        pi.append(a)
    assert sum(pi) == 1
    assert Q(1,2)-F/p**2 >= sum(a*a for a in pi)/4 >= Q(1,4*n)


# Exhaust every three-class binary table and test fractional tables with unequal parts.
for z in product(range(2),repeat=6):
    W = [[0]*3 for _ in range(3)]
    for (i,j),v in zip(combinations_with_replacement(range(3),2),z):
        W[i][j] = W[j][i] = v
    four([2,3,7],W,1)
rng = Random(191117)
for _ in range(160):
    W = [[0]*4 for _ in range(4)]
    for i,j in combinations_with_replacement(range(4),2):
        W[i][j] = W[j][i] = rng.randrange(6)
    four([1,2,7,11],W,5)
print("64 binary and 160 rational tables: bridge and row-collision identities PASS")

# Count labelled RRRB cycles on one paw; the diagonal pairs are unconstrained.
edges = {(0,1),(0,2),(1,2),(2,3)}
def adj(x,y):
    return tuple(sorted((x,y))) in edges
assert sum(adj(x,y) and adj(y,u) and adj(u,v) and not adj(v,x)
           for x,y,u,v in permutations(range(4))) == 4
assert 1-Q(6,5)**2/2 == Q(7,25)
print("Paw contributes four labelled cycles; degree-bin constant PASS")

for k in (2,3,4,7,13,24,40):
    S = 1-Q(1,2**k)
    L = sum((k-d)*Q(1,2**d) for d in range(k))
    m = [2**(k+1-i) for i in range(1,k+1)]+[(2**k-1)*2**j for j in range(1,k+1)]
    W = [[int((i<k and j<k) or (i<k<=j and j-k<=i)
              or (j<k<=i and i-k<=j)) for j in range(2*k)] for i in range(2*k)]
    p,F = raw(m,W)
    assert p == (1+L/S)/4**k
    delta = Q(1,2)-F/p**2
    assert Q(1,8*k) <= delta <= Q(9,k)
    Wpad = [r+[0] for r in W]+[[0]*(2*k+1)]
    pp, FF = raw(m+[sum(m)],Wpad)
    assert pp == p/4 and FF == F/16
    print("k=%2d density, deficit bounds and dilution PASS; k*deficit=%.6f" %
          (k,float(k*delta)))
