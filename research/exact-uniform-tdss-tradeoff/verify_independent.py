#!/usr/bin/env python3
"""Explicit raw joint laws, then exact Bayes prediction; no hypergeom generation."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product

Z, HALF = F(0), F(1, 2)


def measures(joint, n, k, decode):
    keys = defaultdict(F)
    ct = defaultdict(F)
    mc = defaultdict(F)
    correct = defaultdict(F)
    for (x, j, c), p in joint.items():
        keys[x, j] += p
        ct[c] += p
        mc[x, c] += p
        if decode(c, j) == x:
            correct[x, j] += p
    assert sum(ct.values()) == 1
    prior = [sum(keys[x, j] for j in range(k)) for x in range(n)]
    assert all(keys[x, j] == prior[x]/k for x in range(n) for j in range(k))
    return prior, ct, mc, correct


def gains(prior, ct, mc, sets):
    ans = []
    for A in sets:
        p = sum(prior[x] for x in A)
        guess = F(0)
        for c, w in ct.items():
            a = sum(mc[x, c] for x in A)
            guess += max(a, w-a)
        ans.append(guess-max(p, 1-p))
    return ans


def subsets(n):
    return [A for y in range(n+1) for A in combinations(range(n), y)]


runs = truths = keys_checked = 0
for n in range(2, 7):
    for k in range(1, n):
        alph = range(n)
        all_tuples = list(permutations(alph, k))
        sets = subsets(n)
        for s in sorted({F(k, n), F(1), (1+F(k, n))/2, F(1, 2)}):
            if s < F(k, n):
                continue
            J = defaultdict(F)
            branches = [defaultdict(F), defaultdict(F)]
            for x, j in product(alph, range(k)):
                good = [c for c in all_tuples if c[j] == x]
                bad = [c for c in all_tuples if x not in c]
                assert good and bad
                for b, selected, bw in [(0, good, s), (1, bad, 1-s)]:
                    # Unweighted branch measurement is valid even if its coin mass is zero.
                    p = F(1, n*k*len(selected))
                    for c in selected:
                        J[x, j, c] += p*bw
                        branches[b][c] += p
            for branch in branches:
                assert set(branch) == set(all_tuples)
                assert set(branch.values()) == {F(1, len(all_tuples))}
            prior, ct, mc, correct = measures(J, n, k, lambda c, j: c[j])
            assert prior == [F(1, n)]*n
            assert all(correct[x, j] == s/(n*k) for x, j in product(alph, range(k)))
            keys_checked += n*k
            for c in ct:
                # Test both levels and the raw top-list success bound.
                posterior = [mc[x, c]/ct[c] for x in alph]
                assert posterior == [s/k if x in c else (1-s)/(n-k) for x in alph]
                assert max(sum(posterior[x] for x in K) for K in combinations(alph, k)) == s
            observed = gains(prior, ct, mc, sets)
            bysize = {}
            for A, g in zip(sets, observed):
                if len(A) in bysize:
                    assert bysize[len(A)] == g
                bysize[len(A)] = g
            # Independently sum over all (unordered) intersections.
            r = n//2
            hit = [len(set(B) & set(range(r))) for B in combinations(alph, k)]
            bench = sum(abs(s*h/k + (1-s)*(r-h)/(n-k)-HALF) for h in hit)/len(hit)
            bench -= abs(F(r, n)-HALF)
            assert max(observed) == bysize[r] == bench
            runs += 1
            truths += len(sets)

injective = 0
for n in range(1, 5):
    for k in range(n, 7):
        J = defaultdict(F)
        phi_set = list(permutations(range(k), n))
        for x, j in product(range(n), range(k)):
            opts = [phi for phi in phi_set if phi[x] == j]
            for phi in opts:
                J[x, j, phi] += F(1, n*k*len(opts))
        prior, ct, mc, correct = measures(J, n, k, lambda c, j: c.index(j))
        assert set(ct.values()) == {F(1, len(phi_set))}
        assert all(mc[x, c] == w/n for c, w in ct.items() for x in range(n))
        assert sum(correct.values()) == 1
        assert not any(gains(prior, ct, mc, subsets(n)))
        injective += 1

# Nonuniform posterior-law tests, including a threshold hyperplane and ties.
lawtests = 0
for den in range(1, 5):
    kmax = 5
    all_q = [tuple(F(i, den) for i in (x, y, den-x-y))
             for x in range(den+1) for y in range(den-x+1)]
    for q0, q1 in combinations(all_q, 2):
        pws = [(F(2, 5), q0), (F(3, 5), q1)]
        for k in range(1, kmax+1):
            J = defaultdict(F)
            top = []
            h = min(k, 3)
            for a, (w, q) in enumerate(pws):
                T = max(combinations(range(3), h), key=lambda ids: sum(q[x] for x in ids))
                top.append(T)
                injections = list(permutations(range(k), h))
                for phi in injections:
                    for x, xmass in enumerate(q):
                        choices = [phi[T.index(x)]] if x in T else range(k)
                        for j in choices:
                            J[x, j, (a, phi)] += w*xmass/(len(injections)*len(choices))

            def dec(c, j):
                a, phi = c
                return top[a][phi.index(j)] if j in phi else top[a][0]

            prior, ct, mc, correct = measures(J, 3, k, dec)
            assert prior == [sum(w*q[x] for w, q in pws) for x in range(3)]
            for c, w in ct.items():
                assert [mc[x, c]/w for x in range(3)] == list(pws[c[0]][1])
            assert sum(correct.values()) == sum(w*sum(q[x] for x in top[a])
                                                for a, (w, q) in enumerate(pws))
            sets = subsets(3)
            obs = gains(prior, ct, mc, sets)
            assert obs == [sum(w*abs(sum(q[x] for x in A)-HALF) for w, q in pws)
                           - abs(sum(prior[x] for x in A)-HALF) for A in sets]
            lawtests += 1

# A cell containing v=(1/2,1/4,1/4) and u=(1/3,1/3,1/3)
# for all predicates and the top singleton 0. Check affine refinement.
v, u = (HALF, F(1, 4), F(1, 4)), (F(1, 3),)*3
affine = 0
for i in range(1, 10):
    s = F(i, 10)
    q = tuple(s*a+(1-s)*b for a, b in zip(v, u))
    assert max(q) == s*max(v)+(1-s)*max(u)
    for A in subsets(3):
        assert abs(sum(q[x] for x in A)-HALF) == (
            s*abs(sum(v[x] for x in A)-HALF)+(1-s)*abs(sum(u[x] for x in A)-HALF))
        affine += 1

# Negative control: iid decoys do not realize the finite uniform optimum.
N, K = 3, 2
with_replacement = defaultdict(F)
for x, j, dummy in product(range(N), range(K), range(N)):
    pair = (x, dummy) if j == 0 else (dummy, x)
    with_replacement[x, j, pair] += F(1, N*N*K)
p, ct, mc, ok = measures(with_replacement, N, K, lambda c, j: c[j])
assert sum(ok.values()) == 1 and max(gains(p, ct, mc, subsets(N))) == F(1, 9)
print(f"independent PASS: {runs} ordered-tuple laws, {truths} predicate checks, "
      f"{keys_checked} pointwise checks, {injective} injection endpoints")
print(f"independent PASS: {lawtests} nonuniform posterior laws, {affine} affine "
      "refinements, strict iid negative control")
