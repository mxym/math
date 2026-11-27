#!/usr/bin/env python3
"""Exact rational checks for the antiperiodic dual-cutoff note."""
from fractions import Fraction as F
from itertools import combinations, product


def Kentry(d, r, offset):
    j = abs(offset)
    return (r**j-r**(d-j))/(1+r**d)


def inverse_checks(d, r):
    # a=(1+r^2)/r, b=1, kappa=r/(1-r^2).
    # Multiplication by G uses only the two signed neighbors.
    a, kappa = (1+r*r)/r, r/(1-r*r)
    inverse = [[kappa*(-1)**(i+j)*Kentry(d, r, i-j) for j in range(d)] for i in range(d)]
    for i, j in product(range(d), repeat=2):
        left = (i-1) % d
        right = (i+1) % d
        ent = a*inverse[i][j]
        ent += (-1 if i == 0 else 1)*inverse[left][j]
        ent += (-1 if i == d-1 else 1)*inverse[right][j]
        assert ent == (i == j)
    E1 = Kentry(d, r, 0)
    E2 = 2*(E1-Kentry(d, r, 1))
    assert E2 == 2*(1-r)*(1+r**(d-1))/(1+r**d)
    assert (1+r**d)*(E2-E1) == 1-2*r+(2-r)*r**(d-1)
    return d*d


def line_energy(x, r):
    return sum(a*b*r**abs(i-j) for i, a in enumerate(x)
               for j, b in enumerate(x))


def interval_sum(x, l):
    n = len(x)
    return sum(sum(x[max(0, j):min(n, j+l)])**2 for j in range(1-l, n))


def line_checks(r, n=4):
    L, counts = n, 0
    tail = {gap: r**L * ((L+1-gap)*(1-r)+r) for gap in range(n)}
    for x in product(range(-2, 3), repeat=n):
        lhs = line_energy(x, r)
        rhs = (1-r)**2*sum(r**(l-1)*interval_sum(x, l) for l in range(1, L+1))
        rhs += sum(a*b*tail[abs(i-j)] for i, a in enumerate(x)
                   for j, b in enumerate(x))
        assert lhs == rhs
        supp = [i for i in range(n) if x[i]]
        if not supp:
            continue
        if sum(x):
            if len(supp) == 1 and abs(x[supp[0]]) == 1:
                assert lhs == 1
            else:
                assert lhs >= 1+(1-r)**2
        elif (len(supp) == 2 and supp[1]-supp[0] == 1
              and abs(x[supp[0]]) == 1):
            assert lhs == 2*(1-r)
        else:
            assert lhs >= 2*(1-r)+(1-r)**2*min(1, 2*r)
        counts += 1
    return counts


def minimum_checks(d, r):
    S, A1, A2 = [Kentry(d, r, j) for j in range(3)]
    D = 2*(S-A1)
    gamma = (1-r)/(1+r)
    # The proven spectral bound excludes vectors of coefficient norm >=4.
    assert D/gamma < 4
    energies = [[], [], []]
    for k in (1, 2, 3):
        for supp in combinations(range(d), k):
            for sign in product((-1, 1), repeat=k):
                e = k*S+2*sum(sign[u]*sign[v]*Kentry(d, r, supp[v]-supp[u])
                              for u, v in combinations(range(k), 2))
                energies[k-1].append(e)
    assert min(energies[0]) == S and len(energies[0]) == 2*d
    assert min(energies[1]) == D and energies[1].count(D) == 2*d
    t = min(energies[2])
    assert t == 3*S-4*A1+2*A2 and t > D
    return sum(map(len, energies))


def cluster_from_terms(d, terms):
    x = [0]*d
    for i, kind, sign in terms:
        x[i] = sign
        if kind == 2:
            if i+1 == d:
                x[0] = sign  # The backwards sign in the unfolded wrap.
            else:
                x[i+1] = -sign
    return tuple(x)


def get_clusters(d, v, R):
    s = sorted(j for j in range(d) if v[j])
    if not s:
        return []
    gaps = [(s[(i+1)%len(s)]-s[i]) % d or d for i in range(len(s))]
    cuts = [i for i in range(len(s)) if gaps[i] > R]
    out = []
    for u in cuts:
        start = (u+1) % len(s)
        i = start
        while gaps[i] <= R:
            i = (i+1) % len(s)
        length = (i-start) % len(s)+1
        out.append((s[start], length, v[s[start]]))
    return sorted(out)


def clusters_check(d=12, R=2):
    labels = tuple(product(range(d), (1, 2), (-1, 1)))
    output = set()
    for k in range(1, 4):
        for obj in combinations(labels, k):
            sets = [set((i+j)%d for j in range(kind)) for i, kind, _ in obj]
            if any(min((a-b)%d, (b-a)%d) <= R
                   for A, B in combinations(sets, 2) for a in A for b in B):
                continue
            v = cluster_from_terms(d, obj)
            assert v not in output
            output.add(v)
            assert get_clusters(d, v, R) == sorted(obj)
    return len(output)


if __name__ == "__main__":
    inv = line = finite = 0
    for r in (F(1, 3), F(1, 2), F(2, 3), F(4, 5), F(9, 10)):
        line += line_checks(r)
        for d in (4, 6, 8, 12):
            inv += inverse_checks(d, r)
            finite += minimum_checks(d, r)
    cls = clusters_check()
    print(f"PASS: {inv} inverse entries, {line} interval identities and energy gaps, "
          f"{finite} finite shell entries, {cls} compatible configurations")
