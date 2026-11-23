"""Actual eleven-site root geometry applied to both norm-18 seed packings."""
from itertools import combinations, product

def check():
    pairs = list(combinations(range(4), 2))
    stars = [tuple(i for i, p in enumerate(pairs) if h in p) for h in range(4)]
    opposite = [(i, j) for i, j in combinations(range(6), 2)
                if not set(pairs[i]) & set(pairs[j])]
    trip = list(combinations(range(6), 3))
    four = list(combinations(range(6), 4))
    triple_ids = {f: [trip.index(s) for s in combinations(f, 3)] for f in four}

    def cap_all(available):
        best = 0
        uses = [0]*len(trip)
        def search(i, n):
            nonlocal best
            best = max(best, n)
            if n + len(available) - i <= best:
                return
            ts = triple_ids[available[i]]
            if all(uses[k] < 2 for k in ts):
                for k in ts:
                    uses[k] += 1
                search(i+1, n+1)
                for k in ts:
                    uses[k] -= 1
            search(i+1, n)
        search(0, 0)
        return best

    def cap_stars(available):
        ns = [sum(set(s) <= set(f) for f in available) for s in stars]
        return len(available)-sum(ns)+sum(min(x,2) for x in ns)

    base = [(0,1+i) for i in range(4)]
    base += [(1+i,5+k) for k,p in enumerate(pairs) for i in p]
    choices = [[None,*combinations(s,2)] for s in stars]
    choices += [[None,e] for e in opposite]
    all_cases = physical = 0
    best_star = best_all = 0

    for row in product(*choices):
        all_cases += 1
        edges = [e for e in row if e is not None]
        j = sum(e is not None for e in row[:4])
        k = sum(e is not None for e in row[4:])
        adj = [0]*11
        for a,b in base+[(5+i,5+j) for i,j in edges]:
            adj[a] |= 1<<b
            adj[b] |= 1<<a
        if any((adj[a]&adj[b]).bit_count() > 2-(adj[a]>>b&1)
               for a,b in combinations(range(11),2)):
            continue
        physical += 1
        available = [f for f in four if not any(set(e)<=set(f) for e in edges)]
        best_star = max(best_star, 3*cap_stars(available) + 5*j + 6*k)
        best_all = max(best_all, 2*cap_all(available) + 3*j + 3*k)

    assert (all_cases, physical, best_star, best_all) == (2048,1062,33,19)
    P = 851
    J = 8*(99*84-6*P)
    K = 99*336+6*P
    # The coefficients remaining on P after substitution are +204 and +126.
    star_num = 33*55440 - 5*J - 6*K
    all_num = 19*55440 - 3*J - 3*K
    assert (star_num, all_num) == (1470900,861210)
    assert ((star_num//54)*2, (all_num//36)*2) == (54476,47844)
    print('1062 necessary eleven-site charts: N18 <= 54476 (star) or 47844 (all triples).')

if __name__=='__main__':
    check()
