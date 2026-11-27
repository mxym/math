"""Direct subsets and exact group-labelled distance certificates."""
from collections import Counter
from itertools import combinations


def span(vectors):
    W = {0}
    for v in vectors:
        W |= {x ^ v for x in W}
    return frozenset(W)


def dim(X):
    m = len(X)
    assert m > 0 and m & (m-1) == 0 and 0 in X
    return m.bit_length()-1


def hyperplane(n, normal):
    return frozenset(v for v in range(1 << n) if (normal&v).bit_count() % 2 == 0)


def pencil(n, ell):
    low = [frozenset({0})] + sorted({span([ell, a]) for a in range(1 << n)
                                    if a not in (0,ell)}, key=lambda X: tuple(sorted(X)))
    high = [hyperplane(n, a) for a in range(1, 1 << n) if (a&ell).bit_count() % 2]
    assert len(low) == len(high) == 1 << (n-1)
    return low + high


def coordinate(n):
    return [span(1 << j for j in range(n) if a >> j & 1) for a in range(1 << n)]


def fano():
    return [frozenset({0})] + [hyperplane(3, a) for a in range(1, 8)]


def product_line(C, n):
    return C + [frozenset(X | {x ^ (1 << n) for x in X}) for X in C]


def test_code(C):
    assert C[0] == {0}
    assert len(C) == len(set(C))
    d = [dim(X) for X in C]
    for a, X in enumerate(C):
        for b, Y in enumerate(C[:a+1]):
            actual = d[a]+d[b]-2*dim(X & Y)
            if d[a ^ b] != actual:
                return None
    return Counter(d)


def main():
    families = coordinate(4), product_line(fano(), 3), pencil(4, 1)
    assert [tuple(test_code(C)[j] for j in range(5)) for C in families] == [
        (1,4,6,4,1), (1,1,7,7,0), (1,0,7,8,0)]
    bad = families[2].copy()
    bad[1], bad[8] = bad[8], bad[1]
    assert test_code(bad) is None
    print('direct n=4: all three profiles, exact xor-law, bad relabelling rejected')

    pairs = 0
    Hcounts = []
    for n in range(5, 10):
        for ell in (1, (1 << n)-1):
            C = pencil(n, ell)
            dims = test_code(C)
            assert dims == {0: 1, 2: (1<<(n-1))-1, n-1: 1<<(n-1)}
            pairs += len(C)*(len(C)+1)//2
        P = product_line(pencil(n-1, 1), n-1)
        dims = test_code(P)
        assert dims[1] == 1 and dims[n] == 0 and dims[n-1] == 1<<(n-2)
        pairs += len(P)*(len(P)+1)//2
        Hcounts.append((n, 1<<(n-1), dims[n-1]))
    print('direct pencil and sharp product:', Hcounts, '; pair checks', pairs)

    qualifying, examined = 0, 0
    for n in range(2, 5):
        K = set(range(1 << n))
        for m in range(len(K)//4+1, len(K)//2+1):
            for a in combinations(sorted(K), m):
                D = {0} | {x^y for x,y in combinations(a, 2)}
                examined += 1
                if 2*len(D) > len(K):
                    continue
                qualifying += 1
                assert 2*len(D) == len(K) and all(x^y in D for x,y in combinations(D,2))
                assert set(a) <= {a[0]^d for d in D}
    A = (0,1,2,4)
    D = {0} | {x^y for x,y in combinations(A,2)}
    assert len(D) < 8 and 1 in D and 6 in D and 7 not in D
    print('direct doubling n=2..4:', examined, 'subsets;', qualifying, 'qualify; strict boundary control PASS')


if __name__ == '__main__':
    main()
