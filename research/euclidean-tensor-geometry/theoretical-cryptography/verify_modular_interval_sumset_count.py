#!/usr/bin/env python3
"""Finite tests for positive interval-count formulas, not a general polytope solver."""
from collections import Counter
from itertools import product
from math import comb, prod
from random import Random


def signed(lengths):
    out = {0: 1}
    for l in lengths:
        new = Counter(out)
        for a, c in out.items():
            new[a + l] -= c
        out = {a: c for a, c in new.items() if c}
    return out


def dense(lengths):
    d = {0: 1}
    for l in lengths:
        c = Counter()
        for s, v in d.items():
            for x in range(l):
                c[s+x] += v
        d = c
    return d


def pieces(ls):
    mx = sum(l - 1 for l in ls)
    h = sorted(signed(ls).items())
    br = sorted({0, mx+1} | {t for t, c in h if 0 <= t <= mx})
    return [(lo, hi - 1, [(t, c) for t, c in h if t <= lo])
            for lo, hi in zip(br, br[1:])]


def polynomial(terms, n, s):
    return sum(c * comb(s - t + n - 1, n - 1) for t, c in terms)


def progression_count(lengths, q, res):
    # Sum each polynomial along an arithmetic progression using Newton
    # differences and the hockey-stick identity. This tests one dimension.
    n = len(lengths)
    out = 0
    for l, u, terms in pieces(lengths):
        s = l + ((res-l) % q)
        if s > u:
            continue
        m = (u-s)//q + 1
        row = [polynomial(terms, n, s+q*j) for j in range(n)]
        for j in range(n):
            out += row[0]*comb(m, j+1)
            row = [b-a for a,b in zip(row,row[1:])]
    return out


def point_counts():
    count = c2 = pp = 0
    for n in range(1, 6):
        for ls in product(range(1, 6), repeat=n):
            if tuple(sorted(ls)) != ls:
                continue
            d = dense(ls)
            e = {}
            for l, u, terms in pieces(ls):
                for s in range(l, u+1):
                    assert s not in e
                    e[s] = polynomial(terms, n, s)
                    count += 1
            assert e == d and sum(e.values()) == prod(ls)
            for q in (2, 5, 7, 12):
                for r in range(q):
                    assert progression_count(ls, q, r) == sum(
                        v for x, v in d.items() if x % q == r)
                    pp += 1
            c2 += 1
    return count,c2,pp


def composite_joint():
    rng = Random(2827)
    target_cases = points = 0
    for _ in range(72):
        q = rng.choice((4, 6, 8, 9, 10, 12))
        k = rng.randrange(1, 4)
        a = [tuple(rng.randrange(q) for _ in range(2)) for j in range(k)]
        a0 = [rng.randrange(-4,5) for j in range(k)]
        ls = [[rng.randrange(1,4) for i in range(rng.randrange(1,4))]
              for j in range(k)]
        cols = [c for v,lengths in zip(a,ls) for c in (v,)*len(lengths)]
        starts = [s for s,lengths in zip(a0,ls) for t in lengths]
        direct = Counter()
        for x in product(*(range(s, s+l) for s,l in zip(starts, sum(ls,[])))):
            key = tuple(sum(c[h]*v for c,v in zip(cols,x))%q for h in range(2))
            direct[key] += 1
            points += 1
        offset = tuple(sum(v[h]*s*len(l) for v,s,l in zip(a,a0,ls))%q
                       for h in range(2))
        via_pieces = Counter()
        for pset in product(*(pieces(g) for g in ls)):
            for sums in product(*(range(l,u+1) for l,u,t in pset)):
                # The exact congruence in original group coordinates.
                key = tuple((offset[h]+sum(v[h]*s for v,s in zip(a,sums)))%q
                            for h in range(2))
                via_pieces[key] += prod(polynomial(t,len(g),x) for
                    (_,_,t),g,x in zip(pset,ls,sums))
        assert direct == via_pieces
        target_cases += q*q
    return target_cases, points


def difference():
    rng = Random(500)
    tests=0
    for n in range(1,7):
        for _ in range(22):
            w = [rng.randrange(1,5) for i in range(n)]
            M=sum(w)+1
            a=dense([M+v for v in w])
            q=2**((n*M+sum(w)).bit_length())
            assert q>max(a)
            ct=Counter()
            for v in product((0,1),repeat=n):
                ct[sum(x*y for x,y in zip(v,w)),sum(v)] += 1
            for t in range(sum(w)+1):
                for k in range(n+1):
                    b=k*M+t
                    got=sum((-1)**j*comb(n,j)*a.get(b-j,0)
                            for j in range(min(n,b)+1))
                    assert b<q and got==(-1)**k*ct[t,k]
                    tests+=1
    return tests


def bigints():
    tests=0
    for n in range(1,13):
        q=2**(110+n)
        ls=[q*(100+i) for i in range(n)]
        for r in (0,1,q//2,q-1):
            assert q*progression_count(ls,q,r)==prod(ls)
            tests+=1
        shift=q**2
        ls=[shift+q*i for i in range(n)]
        modulus=shift*2**(n+1)
        for t in (0,3,q//3,shift-1):
            assert progression_count(ls,modulus,t)==comb(t+n-1,n-1)
            tests+=1
    return tests



def distance_twice(x, center_twice, q):
    w = (2*x-center_twice)%(2*q)
    return min(w,2*q-w)


def total_variation():
    rng=Random(9781)
    cases=points=0
    for test in range(240):
        n=rng.randrange(1,8)
        q=rng.randrange(2,24)
        ls=[rng.randrange(1,2*q+2) for i in range(n)]
        shift=rng.randrange(-2*q,2*q+1)
        d=dense(ls)
        folded=[sum(v for i,v in d.items() if (i+shift)%q==s)
                for s in range(q)]
        den=prod(ls)
        rem=[a%q for a in ls]
        if all(rem):
            center_twice = 2*shift+sum(a-1 for a in rem)
            shells={}
            for x,v in enumerate(folded):
                k=distance_twice(x,center_twice,q)
                assert k not in shells or shells[k]==v
                shells[k]=v
            radial=[shells[k] for k in sorted(shells)]
            assert radial==sorted(radial,reverse=True)
        else:
            assert all(q*v==den for v in folded)
        # Independent piecewise-wrapped representation on every residue.
        pp=pieces(ls)
        br={0,q}
        for l,u,_ in pp:
            br.update((l%q,u%q+1))
        b=sorted(br)
        vals={}
        for L,R in zip(b,b[1:]):
            bounds=[((l-L+q-1)//q,(u-L)//q,terms) for l,u,terms in pp]
            for r in range(L,R):
                val=sum(polynomial(terms,n,r+q*h) for lo,hi,terms in bounds
                        for h in range(lo,hi+1))
                assert val == folded[(r+shift)%q]
                vals[(r+shift)%q]=val
                points+=1
        exc=[v for v in vals.values() if q*v>den]
        assert 2*q*sum(exc)-2*len(exc)*den == sum(abs(q*v-den) for v in folded)
        cases+=1
    return cases,points


if __name__=="__main__":
    print("PASS: coefficient rows / interval blocks / moment sums /"
          " composite targets and input points / signed differences / bigints / TV")
    print(*point_counts(), *composite_joint(), difference(), bigints(), *total_variation())
