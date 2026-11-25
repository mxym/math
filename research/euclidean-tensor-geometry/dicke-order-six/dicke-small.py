from collections import Counter
from itertools import permutations, product
from math import prod
P = 101
CASES = [
    ((0, 0, 1, 3), (22,)),
    ((0, 1, 2, 3), (48,)),
    ((0, 1, 2, 3, 4), (240, 720)),
    ((0, 0, 0, 1, 1), (16, 28)),
    ((0, 0, 0, 1, 3), (34, 74)),
    ((0, 0, 1, 1, 3), (54, 126)),
    ((0, 0, 1, 3, 9), (114, 306)),
]
def span(rows):
    a = list(map(list, rows))
    r = 0
    for j in range(len(a[0])):
        elt = next((i for i in range(r, len(a)) if a[i][j]), None)
        if elt is None:
            continue
        a[r], a[elt] = a[elt], a[r]
        f = pow(a[r][j], -1, P)
        a[r] = [f * x % P for x in a[r]]
        for b, row in enumerate(a):
            if b != r:
                g = row[j]
                a[b] = [(x - g*y) % P for x, y in zip(row, a[r])]
        r += 1
        if r == len(a):
            break
    return tuple(map(tuple, a[:r]))
def contained(d, rows):
    pivots = [next(j for j, x in enumerate(row) if x) for row in rows]
    return all((x - sum(d[j]*row[i] for j,row in zip(pivots,rows))) % P == 0
               for i,x in enumerate(d))
def run(labels, expected):
    k = len(labels)
    S = sorted(set(permutations(labels)))
    n = len(S)
    m = k - 2
    D = Counter()
    for x, y in product(S, repeat=2):
        if x != y and x[-1] == y[-1]:
            d = tuple((a-b) % P for a,b in zip(x[:m], y[:m]))
            assert any(d)
            D[span([d])[0]] += 1
    spaces = { (d,) for d in D }
    c = prod(v**v for v in Counter(labels).values())
    previous = n
    observed = []
    for r in range(1,m):
        n_r = max(previous, n + max(sum(D[d] for d in D if contained(d, B))
                                    for B in spaces))
        observed.append(n_r)
        assert n_r**(m*k)*k**(r*k) < n**((m+r)*k)*c**r
        if r+1 < m:
            spaces = {C for B in spaces for d in D
                        if len(C := span([*B,d])) == r+1}
        previous = n_r
    assert tuple(observed) == expected
    print(labels,n,observed,flush=True)
if __name__ == "__main__":
    for labels, expected in CASES:
        run(labels, expected)
