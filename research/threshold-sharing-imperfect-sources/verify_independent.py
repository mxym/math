#!/usr/bin/env python3
"""Finite-field sharing checks with Gaussian elimination and direct view counts."""
from collections import Counter
from functools import reduce
from itertools import combinations, product
from math import comb
from operator import xor


class BinaryField:
    def __init__(self, bits, poly):
        self.q = 1 << bits
        self.poly = poly
        self.mul = [[self._multiply(x,y) for y in range(self.q)] for x in range(self.q)]
        self.inv = [None]+[self.mul[x].index(1) for x in range(1,self.q)]

    def _multiply(self, a, b):
        out = 0
        while b:
            if b&1:
                out ^= a
            b >>= 1
            a <<= 1
            if a&self.q:
                a ^= self.poly
        return out

    def inverse_matrix(self, matrix):
        h = len(matrix)
        work = [row[:]+[int(i==j) for j in range(h)] for i,row in enumerate(matrix)]
        for k in range(h):
            i = next((i for i in range(k,h) if work[i][k]),None)
            if i is None:
                return None
            work[k],work[i] = work[i],work[k]
            m = self.mul[self.inv[work[k][k]]]
            work[k] = [m[w] for w in work[k]]
            for i in range(h):
                if i != k and work[i][k]:
                    m = self.mul[work[i][k]]
                    work[i] = [a^m[b] for a,b in zip(work[i],work[k])]
        assert all(x==int(i==j) for i,row in enumerate(work) for j,x in enumerate(row[:h]))
        return [row[h:] for row in work]

    def dot(self,a,b):
        return reduce(xor,(self.mul[x][y] for x,y in zip(a,b)),0)


def prepare(F,n,t,explicit=None):
    # Evaluation points are the first n distinct field elements. Check
    # every allowed active pattern by invertibility of the complete
    # evaluation/secret matrix, without using barycentric weights.
    Asets = list(combinations(range(n),t))
    basis = []
    for x in range(n):
        row = [1]
        for _ in range(1,t-1):
            row.append(F.mul[x][row[-1]])
        basis.append(row)

    def matrix(A, B, gamma):
        return [basis[j]+[gamma[j] if j in B else 0] for j in A]

    grouping = [[] for _ in range(n)]
    all_constraints = []
    for A in Asets:
        for k in range(1,t+1):
            for B in combinations(A,k):
                grouping[B[-1]].append((A,B))
                all_constraints.append((A,B))
    assert max(map(len,grouping)) == (1<<(t-1))*comb(n-1,t-1)
    assert len(all_constraints) == comb(n,t)*((1<<t)-1)
    assert F.inverse_matrix(matrix(*all_constraints[0],[0]*n)) is None

    if explicit is None:
        assert F.q > max(map(len,grouping)) and F.q >= n
        gamma = [0]*n
        for j in range(n):
            good = []
            for val in range(F.q):
                gamma[j] = val
                if all(F.inverse_matrix(matrix(A,B,gamma)) is not None for A,B in grouping[j]):
                    good.append(val)
            assert len(good) >= F.q-len(grouping[j]) > 0
            gamma[j] = good[0]
    else:
        gamma = list(explicit)

    rows = {}
    for A,B in all_constraints:
        inv = F.inverse_matrix(matrix(A,B,gamma))
        assert inv is not None,(A,B,gamma)
        rows[A,B] = inv[-1]
    return basis,gamma,rows


def remove_zero(counter):
    return {k:v for k,v in counter.items() if v != 0}


def enumerate_instance(F,n,t,multiplicities,explicit=None):
    basis,gamma,decoders = prepare(F,n,t,explicit)
    q = F.q
    pads = [tuple(F.dot(basis[j],u) for j in range(n))
            for u in product(range(q),repeat=t-1)]
    Jsets = [J for s in range(t) for J in combinations(range(n),s)]
    Asets = list(combinations(range(n),t))
    # Small test cases have independently tabulated multiplicities by size.
    # Each row is a nonnegative number of actual labeled copies.
    patterns = [(frozenset(D),int(c<0),abs(c)) for k,c in enumerate(multiplicities)
                for D in combinations(range(n),k)]
    assert sum((-1)**g*a for _,g,a in patterns) == 1
    reconstruct = local_equal = full_sources = 0
    ref_local = {}
    ref_base = None
    ref_full = {}
    explicit_selectors = len(pads) <= 4
    for m in range(q):
        base = [Counter() for _ in Jsets]
        per_index = []
        for u,v in enumerate(pads):
            local = [[Counter() for _ in Jsets] for _ in range(2)]
            for D,branch,copies in patterns:
                shares = tuple((int(j in D),v[j]^(F.mul[gamma[j]][m] if j not in D else 0))
                               for j in range(n))
                assert all(tag in (0,1) and 0 <= z < q for tag,z in shares)
                for A in Asets:
                    B = tuple(j for j in A if shares[j][0]==0)
                    ys = [shares[j][1] for j in A]
                    assert F.dot(decoders[A,B],ys) == m
                    reconstruct += copies
                for l,J in enumerate(Jsets):
                    obs = tuple(shares[j] for j in J)
                    local[branch][l][obs] += copies
            for l in range(len(Jsets)):
                p,neg = local[0][l],local[1][l]
                base[l].update(neg)
                ds = p.copy()
                ds.subtract(neg)
                signed=remove_zero(ds)
                if m==0:
                    ref_local[u,l]=signed
                else:
                    assert ref_local[u,l]==signed
                    local_equal += 1
            if explicit_selectors:
                per_index.append(local)
        if m==0:
            ref_base=base
        else:
            assert ref_base==base
        # For a large pad set this all-minus count and all individual
        # signed index counts certify every support choice by additivity.
        # Where small, additionally test every source choice by its actual
        # histogram and its common normalization.
        if explicit_selectors:
            for selector in range(1<<len(pads)):
                for l in range(len(Jsets)):
                    hist=Counter()
                    for u,local in enumerate(per_index):
                        hist.update(local[0 if (selector>>u)&1 else 1][l])
                    total=sum(hist.values())
                    assert total == len(pads)*sum(c for _,g,c in patterns if g==1)+selector.bit_count()
                    if m==0:
                        ref_full[selector,l]=hist
                    else:
                        assert ref_full[selector,l]==hist
                        full_sources += 1
    return len(decoders),reconstruct,local_equal,full_sources


if __name__ == "__main__":
    total_decoders=total_rec=total_deltas=total_full=0
    for b,poly,n,t,counts,explicit in [
        (2,0x7,2,2,(-1,1),None),
        (2,0x7,3,2,(-2,1),(1,2,3)),
        (3,0xb,3,3,(1,-1,1),None),
        (4,0x13,4,3,(3,-2,1),None),
    ]:
        nd,nr,np,nf=enumerate_instance(BinaryField(b,poly),n,t,counts,explicit)
        total_decoders+=nd
        total_rec+=nr
        total_deltas+=np
        total_full+=nf
    for b,poly,n,t in [(6,0x43,5,4),(6,0x43,6,4),(6,0x43,6,5)]:
        # The last two cases below may need a larger field. Select the
        # least extension among our checked representations meeting (2).
        cutoff=(1<<(t-1))*comb(n-1,t-1)
        if (1<<b) <= cutoff:
            b,poly=(7,0x83) if cutoff < 128 else (8,0x11b)
        _,_,ds=prepare(BinaryField(b,poly),n,t)
        total_decoders+=len(ds)
    print(f"independent PASS: {total_decoders} field decoder matrices over every authorized active pattern")
    print(f"independent PASS: {total_rec} authorized secret/key reconstructions (labeled copies counted)")
    print(f"independent PASS: {total_deltas} exact signed histograms and all-base counts certify all source choices")
    print(f"independent PASS: {total_full} separately enumerated full-source histogram comparisons")
