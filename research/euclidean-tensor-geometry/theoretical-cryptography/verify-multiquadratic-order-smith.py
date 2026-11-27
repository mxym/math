#!/usr/bin/env python3
"""Exact branch-evaluation and local Smith checks for multiquadratic orders."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb


def v_p(x, p):
    x = Fraction(x)
    if not x:
        return float("inf")
    a, b, t = x.numerator, x.denominator, 0
    while a % p == 0:
        a //= p
        t += 1
    while b % p == 0:
        b //= p
        t -= 1
    return t


def smith_valuation(matrix, p):
    a = [[Fraction(x) for x in row] for row in matrix]
    n, out = len(a), []
    assert all(len(row) == n for row in a)
    for k in range(n):
        val, i, j = min((v_p(a[i][j], p), i, j)
                        for i in range(k, n) for j in range(k, n))
        assert val >= 0 and a[i][j]
        out.append(val)
        a[k], a[i] = a[i], a[k]
        for row in a:
            row[k], row[j] = row[j], row[k]
        for i1 in range(k+1, n):
            if not a[i1][k]:
                continue
            s = a[i1][k]/a[k][k]
            assert v_p(s, p) >= 0
            for j1 in range(k+1, n):
                a[i1][j1] -= s*a[k][j1]
            a[i1][k] = 0
    assert sorted(out) == out
    return out


def mul(a, b, leading):
    n = len(a)
    ans = [0]*n
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            q, s = divmod(i+j, n)
            ans[s] += x*y*(leading if q else 1)
    return tuple(ans)


def evaluate(roots, degree, leading, anchor):
    n = len(roots)
    extras = [j for j in range(n) if j not in anchor]
    cols = []
    for expo in product(range(2), repeat=n):
        monomial = (1,)+(0,)*(degree-1)
        for j, e in enumerate(expo):
            if e:
                monomial = mul(monomial, roots[j], leading)
        col = []
        for signs in product((-1, 1), repeat=len(extras)):
            s = 1
            for j, sgn in zip(extras, signs):
                if expo[j]:
                    s *= sgn
            col.extend(s*a for a in monomial)
        cols.append(col)
    return list(zip(*cols))


def anchor_for(types):
    if not types:
        return []
    tset = set(types)
    if len(tset)==1:
        return [0]
    if "A" in tset:
        return [types.index("A"), types.index("B" if "B" in tset else "C")]
    return [types.index("B"), types.index("C")]


def canonical2(types):
    anchor = anchor_for(types)
    if not anchor:
        return [[1]]
    if len(anchor)==1:
        return evaluate([(0,1)]*len(types), 2, {"A":-1, "B":2, "C":-2}[types[0]], anchor)
    roots = {"A":(0,0,1,0), "B":(0,1,0,-1), "C":(0,1,0,1)}
    return evaluate([roots[t] for t in types], 4, -1, anchor)


def predicted2(types, anchor=None):
    if anchor is None:
        anchor = anchor_for(types)
    if not anchor:
        return [0]
    emb = [types[j] for j in anchor]
    if len(emb)==1:
        P = ((0,0), (0,1))
    elif "A" in emb:
        P = ((0,0,0,1), (0,1,1,1))
    else:
        P = ((0,0,1,1), (0,1,1,2))
    extras = [t for j,t in enumerate(types) if j not in anchor]
    out = []
    for show in product(range(2), repeat=len(extras)):
        h = sum(s for t,s in zip(extras,show) if t in "BC")
        out.extend(sum(show)+h//2+x for x in P[h%2])
    return sorted(out)


def check_discriminant(types, exps, p):
    # Summing character discriminants includes the trivial class,
    # which has exponent zero. Independent of the anchor choice.
    d = {"U":0, "A":1, "B":2, "C":3}
    weights = (0,2,3,3) if p==2 else (0,0,1,1)
    a = 2**max(0,len(types)-1)*sum(weights[d[t]] for t in types)
    b = 0
    for bits in product(range(2), repeat=len(types)):
        g = 0
        for s,t in zip(bits,types):
            if s:
                g ^= d[t]
        b += weights[g]
    assert a-b == 2*sum(exps)


def check_mod_kernel(matrix, exps, p, e):
    q, d = p**e, len(matrix)
    expect = p**sum(min(e,s) for s in exps)
    image = {
        tuple(sum(x*y for x,y in zip(row,v))%q for row in matrix)
        for v in product(range(q),repeat=d)
    }
    assert len(image)*expect == q**d


if __name__ == "__main__":
    n = 0
    for counts in product(range(5),repeat=3):
        if sum(counts)>5:
            continue
        types = sum(([t]*k for t,k in zip("ABC",counts)),[])
        A = canonical2(types)
        exps = smith_valuation(A,2)
        assert exps == predicted2(types)
        check_discriminant(types,exps,2)
        for u in range(3):
            check_discriminant(types+["U"]*u,exps*2**u,2)
        if all(t in types for t in "ABC"):
            assert exps == predicted2(types,[types.index("A"),types.index("C")])
        if len(types)<=2:
            check_mod_kernel(A,exps,2,1)
            check_mod_kernel(A,exps,2,2)
        n += 1
    for types in ("AAAAAA","BBBBBB","AABBCC","BBBCCC"):
        p = predicted2(types)
        assert p == smith_valuation(canonical2(types),2)
        check_discriminant(types,p,2)
        n += 1
    assert [predicted2(t) for t in ["AB","BC","BB","ABC"]] == [
        [0,0,0,1],[0,0,1,1],[0,0,1,2],[0,0,0,1,1,2,2,2]]
    odd = 0
    for p in (3,5,7):
        for k in range(1,6):
            M = evaluate([(0,1)]*k,2,p,[0])
            es = smith_valuation(M,p)
            assert es == [j//2 for j in range(k+1) for _ in range(comb(k,j))]
            check_discriminant(["B"]*k,es,p)
            if k<=2:
                check_mod_kernel(M,es,p,1)
            odd += 1
    print(f"PASS: {n} complete dyadic Smith matrices, {odd} odd-prime Smith matrices, "
          "anchor choices, discriminants and bounded quotient checks")
