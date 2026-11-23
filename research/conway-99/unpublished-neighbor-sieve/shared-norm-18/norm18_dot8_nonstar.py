"""Verify the all-three-label packing cap by exact local counting."""
from itertools import combinations, product

def check():
    labels = list(combinations(range(4), 2))
    stars = [tuple(i for i, p in enumerate(labels) if a in p) for a in range(4)]
    opposite = [(i, j) for i, j in combinations(range(6), 2)
                if not set(labels[i]) & set(labels[j])]
    triples = list(combinations(range(6), 3))
    fours = list(combinations(range(6), 4))
    windows = [(sum(1 << i for i in s),
                tuple(triples.index(t) for t in combinations(s, 3))) for s in fours]

    def capacity(eligible):
        counts = [0] * len(triples)
        best = 0
        def visit(i, used):
            nonlocal best
            best = max(best, used)
            if used + len(eligible) - i <= best:
                return
            ts = eligible[i]
            if all(counts[t] < 2 for t in ts):
                for t in ts:
                    counts[t] += 1
                visit(i+1, used+1)
                for t in ts:
                    counts[t] -= 1
            visit(i+1, used)
        visit(0, 0)
        return best

    choices = [[None, *combinations(st, 2)] for st in stars]
    choices += [[None, e] for e in opposite]
    n = 0
    table = {}
    for edges in product(*choices):
        j = sum(e is not None for e in edges[:4])
        k = sum(e is not None for e in edges[4:])
        masks = [(1 << e[0]) | (1 << e[1]) for e in edges if e is not None]
        cap = capacity([ts for s, ts in windows if not any(e & s == e for e in masks)])
        table[j,k] = max(table.get((j,k), 0), cap)
        assert 3*cap + 4*j + 4*k <= 28
        n += 1
    assert n == 2048
    assert [[table[j,k] for k in range(4)] for j in range(5)] == [
        [9,8,4,0],[8,5,3,0],[5,5,2,0],[3,2,1,0],[2,1,0,0]]
    bound = 28*55440 - 32*(99*84-6*851) - 4*(99*336+6*851)
    assert bound // 27 == 48004
    print(n, "exact seed charts: given N16=U127=0, oriented N18 <= 48004.")

if __name__ == "__main__":
    check()
