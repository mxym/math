"""Direct codeword and adjacency verification; rational interpolation."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product

I4 = (0, 1, 2, 3)
I3s = tuple(combinations(I4, 3))


def norm2(v):
    return sum(x*x for x in v)


def scalar_product(a, b):
    return sum(x*y for x, y in zip(a, b))


def signed(r, p):
    r %= p
    return r-p if r > p//2 else r


def verify(L, p, g):
    n11, n12, n22 = g
    unit = tuple(product((-1, 0, 1), repeat=L))
    F = [(a, b) for a in unit for b in unit
         if (norm2(a), scalar_product(a, b), norm2(b)) == g]
    alphabet = tuple(product(range(p), repeat=L))
    C = set()
    for z in alphabet:
        for a, b in F:
            C.add(tuple(tuple((zi + j*ai + j*j*bi) % p
                              for zi, ai, bi in zip(z, a, b)) for j in I4))
    assert len(C) == p**L * len(F)
    all_projections = {}
    graph = {(i, j): defaultdict(set) for i, j in combinations(I4, 2)}
    for word in C:
        for (i, j), table in graph.items():
            table[word[i]].add(word[j])
    n_tri = 0
    n_four = 0
    interp = 0
    for I in I3s + (I4,):
        for k in range(len(I)):
            i = I[k]
            assert set().union(*(set(graph[i,j]) for j in I[k+1:])) <= set(alphabet)
        i, j, k = I[:3]
        if (i, j, k) not in all_projections:
            all_projections[i, j, k] = set()
            for a in alphabet:
                for b in graph[i, j].get(a, ()):
                    for c in graph[i, k].get(a, set()) & graph[j, k].get(b, set()):
                        all_projections[i, j, k].add((a, b, c))
            assert all_projections[i, j, k] == {tuple(w[t] for t in (i,j,k)) for w in C}
            assert len(all_projections[i, j, k]) == len(C)
            n_tri += len(all_projections[i, j, k])
            # Check absolute triples at more than one origin, recovering
            # the two coefficients by the standard quadratic linear system,
            # without computing or dividing integer secant witnesses.
            for a, b, c in sorted(all_projections[i, j, k]):
                if any(x != 1 for x in a) and any(x != 0 for x in a):
                    continue
                u = [signed(y-x,p) for x,y in zip(a,b)]
                v = [signed(y-x,p) for x,y in zip(a,c)]
                det = (j-i)*(k*k-i*i) - (k-i)*(j*j-i*i)
                A = [Fraction((k*k-i*i)*x - (j*j-i*i)*y, det) for x,y in zip(u,v)]
                B = [Fraction((j-i)*y - (k-i)*x, det) for x,y in zip(u,v)]
                assert all(z.denominator == 1 for z in A+B)
                assert (norm2(A), scalar_product(A,B), norm2(B)) == g
                interp += 1
        if len(I) == 4:
            l = I[-1]
            W = set()
            for a,b,c in all_projections[i,j,k]:
                D = graph[i,l].get(a,set()) & graph[j,l].get(b,set()) & graph[k,l].get(c,set())
                W.update((a,b,c,last) for last in D)
            assert W == C
            n_four += len(W)
    print(f"Direct L={L}, P={p}, Gram={g}: codes={len(C)}, "
          f"all-position triangles={n_tri}, 4-cliques={n_four}, rational recoveries={interp}")


if __name__ == "__main__":
    for case in ((1,41,(0,0,0)), (1,41,(1,1,1)), (1,43,(1,-1,1)),
                 (2,73,(1,0,1)), (2,73,(2,0,2))):
        verify(*case)
