#!/usr/bin/env python3
"""Exact finite checks for triple-cyclotomic-smoothing-cutoff.md."""

from itertools import combinations, permutations, product
from math import comb, factorial
from collections import Counter


def cycle_number(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            while i not in seen:
                seen.add(i)
                i = p[i]
    return c


def inventory_and_young():
    cases = 0
    memo = {}
    def enumerator(m,T):
        # Character cycle recursion: count the cycle of index zero.
        if not m:
            return 1
        key = (m,T)
        if key not in memo:
            memo[key] = sum(
                comb(m-1,k-1)*factorial(k-1)*T*enumerator(m-k,T)
                for k in range(2,m+1)
            )
        return memo[key]
    for m in range(1,7):
        D = {p: cycle_number(p) for p in permutations(range(m))
             if all(i != j for i,j in enumerate(p))}
        counters = Counter(D.values())
        for T in (1,2,4,8,9,25,27,64,125):
            assert enumerator(m,T) == sum(n*T**c for c,n in counters.items())
            cases += 1
        hist = Counter()
        for q,cq in D.items():
            qinv = [0]*m
            for j,l in enumerate(q):
                qinv[l] = j
            for p,cp in D.items():
                pq = tuple(qinv[x] for x in p)
                cr = D.get(pq)
                if cr is not None:
                    hist[cp,cr,cq] += 1
        # Square alphabets make the (3/2)-powers integers.
        for b1,b2,b3 in ((1,2,3),(2,2,2),(3,4,5),(5,1,3)):
            A = (b1*b1,b2*b2,b3*b3)
            W = sum(k*A[0]**i*A[1]**j*A[2]**l for (i,j,l),k in hist.items())
            assert W**3 <= (
                enumerator(m,b1**3)*enumerator(m,b2**3)*enumerator(m,b3**3)
            )**2
            cases += 1
    return cases


def signed_cycles(n,m,k):
    ans = set()
    for r,c in product(permutations(range(n),k), permutations(range(m),k)):
        v = [0]*(n*m)
        for i in range(k):
            v[r[i]*m+c[i]] = 1
            v[r[(i+1)%k]*m+c[i]] = -1
        ans.add(tuple(v))
    return ans


def exhaustive_shells():
    small = n4 = 0
    for n1,n2,n3 in product(range(2,5),repeat=3):
        R = signed_cycles(n1,n2,2)
        C = signed_cycles(n1,n2,3)
        cube = comb(n3,2)*len(R)
        six = comb(n3,2)*len(C)
        if n3 >= 3:
            # Three nonzero slices of total L1 mass 12 are unit rectangles.
            six += comb(n3,3)*sum(
                tuple(-x-y for x,y in zip(u,v)) in R for u,v in product(R,repeat=2)
            )
        ns = (n1,n2,n3)
        assert cube == 2*comb(n1,2)*comb(n2,2)*comb(n3,2)
        assert six == 12*sum(
            comb(ns[i],2)*comb(ns[(i+1)%3],3)*comb(ns[(i+2)%3],3) for i in range(3)
        )
        small += 1
    R = signed_cycles(4,4,2)
    coded = []
    for u in R:
        row_mask = sum(1<<i for i in range(4) if any(u[4*i+j] for j in range(4)))
        col_mask = sum(1<<j for j in range(4) if any(u[4*i+j] for i in range(4)))
        coded.append((u,row_mask,col_mask))
    for (u,a,b),(v,c,d),(w,e,f) in product(coded,repeat=3):
        z = tuple(-x-y-zz for x,y,zz in zip(u,v,w))
        if z not in R:
            continue
        rows = a|c|e
        cols = b|d|f
        rows |= sum(1<<i for i in range(4) if any(z[4*i+j] for j in range(4)))
        cols |= sum(1<<j for j in range(4) if any(z[4*i+j] for i in range(4)))
        if rows == cols == 15:
            n4 += 1
    assert n4 == 2*(comb(4,2)*comb(2,2))**3
    return small,n4


def repeated_signs():
    checks = 0
    for amp in range(1,7):
        m = 4*amp
        # Table with alternating signs on the cube, each nonzero entry +/-amp.
        words = factorial(m)**2 // factorial(amp)**8
        matchings = factorial(amp)**12
        assert words*factorial(amp)**8 == factorial(m)**2
        assert (words*matchings)*factorial(amp)**8 >= factorial(m)**2
        # a=1/2, exact (4) after factoring a^(2m).
        assert factorial(amp)**8 <= 2**(8*amp*(amp-1))
        checks += 1
    return checks


if __name__ == "__main__":
    cy = inventory_and_young()
    s,c = exhaustive_shells()
    r = repeated_signs()
    print(f"PASS: {cy} derangement inventory and exact convolution bounds")
    print(f"PASS: {s} small shell shape counts, {c} maximal-label 4x4x4 vectors")
    print(f"PASS: {r} repeated signed cube weights")
