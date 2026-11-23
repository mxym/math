"""Count labelled induced subgraphs through six vertices as affine functions of P."""
from collections import Counter
from functools import cache
from itertools import combinations
from math import factorial, perm


@cache
def edges(n):
    return tuple(combinations(range(n), 2))


@cache
def partitions(n):
    if n == 0:
        return ((),)
    return tuple(part + (block,) for part in partitions(n - 1)
                 for block in range(max(part, default=-1) + 2))


def quotient(n, mask, part):
    size = max(part, default=-1) + 1
    bits = 0
    for i, (u, v) in enumerate(edges(n)):
        if mask & (1 << i):
            a, b = sorted((part[u], part[v]))
            if a == b:
                return None
            bits |= 1 << edges(size).index((a, b))
    return size, bits


def census(prisms):
    @cache
    def noninjective(n, mask):
        total = 0
        for part in partitions(n):
            if len(set(part)) < n:
                smaller = quotient(n, mask, part)
                if smaller is not None:
                    total += injective(*smaller)
        return total

    @cache
    def hom(n, mask):
        if n == 0:
            return 1
        adj = [set() for _ in range(n)]
        for i, (u, v) in enumerate(edges(n)):
            if mask & (1 << i):
                adj[u].add(v)
                adj[v].add(u)
        root = min(range(n), key=lambda u: len(adj[u]))
        degree = len(adj[root])
        if degree >= 3:
            prism = (n == 6 and all(len(row) == 3 for row in adj)
                     and any(adj[u] & adj[v] for u in range(n) for v in adj[u]))
            return noninjective(n, mask) + (12 * prisms if prism else 0)
        points = [u for u in range(n) if u != root]
        sub = sum(1 << i for i, (u, v) in enumerate(edges(n - 1))
                  if points[v] in adj[points[u]])
        base = hom(n - 1, sub)
        if degree == 0:
            return 99 * base
        if degree == 1:
            return 14 * base
        u, v = sorted(points.index(p) for p in adj[root])
        add_edge = 1 << edges(n - 1).index((u, v))
        part = tuple(u if p == v else p - int(p > v) for p in range(n - 1))
        merged = quotient(n - 1, sub, part)
        diagonal = hom(*merged) if merged is not None else 0
        return 2 * base - hom(n - 1, sub | add_edge) + 12 * diagonal

    @cache
    def injective(n, mask):
        return hom(n, mask) - noninjective(n, mask)

    @cache
    def induced(n):
        values = [injective(n, mask) for mask in range(1 << len(edges(n)))]
        for i in range(len(edges(n))):
            for mask in range(len(values)):
                if not mask & (1 << i):
                    values[mask] -= values[mask | (1 << i)]
        assert sum(values) == perm(99, n)
        return values


    result=Counter()
    for n in range(7):
        for plus in range(n+1):
            minus=n-plus; s=plus-minus
            if abs(s)>5:continue
            cc=Counter()
            for mask,k in enumerate(induced(n)):
                if not k:continue
                e=sum((1 if (a<plus)==(b<plus) else -1) for i,(a,b) in enumerate(edges(n)) if mask>>i&1)
                cc[e]+=k
            div=factorial(plus)*factorial(minus)
            for e,k in cc.items():
                assert not k%div
                for v in range(-6,7):
                    for w in range(-4,5):
                        j=2*n+e+w*s+v*v+v*w+3*w*w
                        if 0<=j<=9:result[j]+=k//div
    return [result[i] for i in range(10)]

def fiber_types(j):
    # For 2j <= 18, 7 Q(p,q) <= 198+225 and Q >= 5p^2+q^2.
    hist = Counter()
    for a in range(-5, 6):
        for p in range(-8, 9):
            for q in range(-8, 9):
                if (a+p-2*q)%11:
                    continue
                delta=7*(6*p*p-2*p*q+2*q*q)-9*a*a
                assert delta%11==0
                t=2*j-delta//11
                if t>=9*abs(a) and (t-a)%2==0:
                    hist[abs(a),t]+=1
    return dict(hist)

if __name__=='__main__':
    for j in range(6):
        assert fiber_types(j)=={(0,2*j):1}
    assert fiber_types(6)=={(0,12):1,(1,9):4}
    assert fiber_types(7)=={(0,14):1,(1,11):4,(0,0):2}
    assert fiber_types(8)=={(0,16):1,(0,2):2,(1,13):4,(2,18):2}
    assert fiber_types(9)=={(0,18):1,(0,4):2,(1,15):4,(2,20):2}
    base=census(0)
    slope=[x-y for x,y in zip(census(1),base)]
    assert base==[1,2,198,1786,40592,773392,14385096,164667888,
                  1254825198,6155557260]
    assert slope==[0,0,0,0,0,6,-54,180,-126,-1096]
    print('dual fiber table verified through norm 18')
    print('mandatory primal contributions by half-norm: base + P * slope')
    print('base ',base)
    print('slope',slope)
