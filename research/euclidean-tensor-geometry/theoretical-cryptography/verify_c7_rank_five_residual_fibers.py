#!/usr/bin/env python3
"""Exact checker for C7RankFiveResidualFibers.md. Python >=3.8, stdlib only."""

from base64 import b85decode
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from json import loads
from pathlib import Path
from struct import iter_unpack
from zlib import decompress

D = (0, 1, 6)
E = (0, 1, 2, 3, 4, 5, 6)
Q3 = ((1, 0), (0, 1), (0, 2), (1, 1), (2, 4), (3, 0), (3, 3))
LO = (2000000000, 1246979603, -445041868, -1801937736,
      -1801937736, -445041868, 1246979603)
Q4 = ((1, 1, 0, 2, 3), (1, 1, 1, 2, 3), (1, 1, 2, 2, 3),
      (1, 1, 1, 0, 3), (1, 1, 1, 1, 3), (1, 1, 1, 3, 3))
OCTAVE = Fraction(331767, 100000)


def check(cond, what):
    if not cond:
        raise AssertionError(what)


def neg(v):
    return tuple(-z % 7 for z in v)


def rep(v):
    return min(v, neg(v))


def dot(u, v):
    return sum(a*b for a, b in zip(u, v)) % 7


def check_thresholds():
    for i, s in ((1, 1), (2, -1), (3, 1)):
        a = Fraction(LO[i], 10**9)
        b = Fraction(LO[i]+1, 10**9)
        def f(x):
            return x**3 + x**2 - 2*x - 1
        check(s*f(a) < 0 < s*f(b), ('cos bracket', i))
    check((OCTAVE/(7-OCTAVE))**2 > (2+Fraction(LO[1]+1, 10**9))/4,
          'C7 theta rational upper')
    check(OCTAVE**9 < 3*7**5, 'rank-four 9 columns')
    check(OCTAVE**6 < Fraction(39, 10)*7**3 < 4*7**3, 'rank-three 6 columns')
    check(OCTAVE**8 < Fraction(3057, 500)*7**4 < 7*7**4, 'rank-four 8 columns')


def make_fibers(dim):
    V = list(product(E, repeat=dim))
    ind = {x:i for i,x in enumerate(V)}
    perm = [[ind[tuple((a+b)%7 for a,b in zip(x,z))] for z in V] for x in V]
    def peak(cols):
        c = [1]+[0]*(len(V)-1)
        for u in cols:
            d = c.copy()
            for j,k in enumerate(perm[ind[u]]):
                d[k] += c[j]
            c = d
        return max(c)
    return peak, [u for u in V if u == rep(u)]


def canon_plane(cols):
    opts = []
    for (a,b), (c,d) in product(cols, repeat=2):
        det = (a*d-b*c) % 7
        if det == 0:
            continue
        k = pow(det,-1,7)
        for s,t in product((1,-1), repeat=2):
            opts.append(tuple(sorted(
                rep((s*k*(d*x-c*y)%7,t*k*(a*y-b*x)%7)) for x,y in cols
            )))
    return min(opts)


def verify_projected_plane():
    peak, signs = make_fibers(2)
    classes = Counter()
    count = 0
    for extra in combinations_with_replacement(signs, 5):
        cols = ((1,0),(0,1))+extra
        count += 1
        if peak(cols) <= 3:
            classes[canon_plane(cols)] += 1
    check(count == 118755 and classes == {canon_plane(Q3):72}, 'projected plane')


def verify_projected_line():
    peak, signs = make_fibers(1)
    wrappers = set()
    for extra in combinations_with_replacement(signs, 4):
        cols = ((1,),)+extra
        if peak(cols) <= 6:
            wrappers.add(min(tuple(sorted(rep((z*u[0]%7,))[0] for u in cols)) for z in E[1:]))
    check(wrappers == {tuple(sorted(q)) for q in Q4}, 'projected line')


def signset(proj, k):
    """Nonzero signed vectors in ker(proj), encoded by free coordinates."""
    out = []
    for z in product(D, repeat=len(proj)-k):
        if any(z) and all(-sum(a*q[i] for a,q in zip(z,proj[k:])) % 7 in D
                          for i in range(k)):
            out.append(z)
    return set(out)


def check_fourier(coeff, denom, residues, target):
    check(all(isinstance(k,int) and k >= 0 for k in coeff), 'nonnegative weights')
    check(1 + Fraction(2*sum(coeff), denom) >= target, 'Fourier objective')
    for row in residues:
        check(sum(a*b for a,b in zip(row, coeff)) >= -denom*10**9,
              'Fourier lower interval')


def check_rank_three(data):
    S = signset(Q3, 2)
    P = sorted(s for s in S if s == rep(s))
    check(len(S) == 44 and len(P) == 22, 'signed support')
    arrays = []
    for q in data:
        coeff = tuple(x[0] for x in iter_unpack('<H', decompress(b85decode(q))))
        check(len(coeff)%len(P) == 0, 'packed weight length')
        arrays.append(iter([coeff[j:j+len(P)] for j in range(0,len(coeff),len(P))]))
    check(len(arrays) == 8, 'witness shard count')

    V = list(product(E, repeat=3))
    ind = {v:i for i,v in enumerate(V)}
    d = [[ind[tuple((a-b)%7 for a,b in zip(u,v))] for v in V] for u in V]
    chars = [u for u in V if u == rep(u)]
    tables = [[LO[dot(u,v)] for v in V] for u in chars]

    def clique4(Z):
        L = sorted(Z)
        for i,u in enumerate(L):
            nbr = [v for v in L[i+1:] if d[v][u] in Z]
            for j,v in enumerate(nbr):
                if any(d[w][v] in Z for w in nbr[j+1:]):
                    return True
        return False

    stats = Counter()
    for u,v in combinations(range(5),2):
        piv = (u,v)
        free = [[j for j in range(p+1,5) if j not in piv] for p in piv]
        rest = [j for j in range(5) if j not in piv]
        for lab in product(E, repeat=sum(map(len,free))):
            rows = [[int(i==p) for i in range(5)] for p in piv]
            for row,idxs,start in zip(rows,free,(0,len(free[0]))):
                for j,value in zip(idxs,lab[start:]):
                    row[j] = value
            a,b = rows
            def sy(z):
                return ind[tuple((z[j]-z[u]*a[j]-z[v]*b[j])%7 for j in rest)]
            stats['kernels'] += 1
            # We only need one image from every signed pair. Their opposites
            # are accounted for explicitly in the Cayley connection set.
            im = [sy(s) for s in P]
            if 0 in im:
                continue
            stats['dissociated'] += 1
            Z = set(im)
            Z.update(d[0][v] for v in im)
            if not clique4(Z):
                stats['witnesses'] += 1
                sh = lab[0] if piv == (0,1) else 7
                ck = next(arrays[sh])
                check_fourier(ck, 1000, ([row[v] for v in im] for row in tables),
                              Fraction(39,10))
    check(all(next(q,None) is None for q in arrays), 'no unused weights')
    check(stats == {'kernels':140050, 'dissociated':131469, 'witnesses':1498},
          ('kernel counts',stats))


def check_rank_four(data):
    good = {q for q in Q4 if q not in ((1,1,1,2,3),(1,1,2,2,3))}
    seen = set()
    for raw_q, coeff in data:
        q = tuple(raw_q)
        check(q in good and q not in seen, 'hyperplane certificate labels')
        seen.add(q)
        # The kernel of the first row of the quotient matrix is identified
        # with its four free coordinates, since q[0] = 1.
        support = sorted(s for s in signset(tuple((v,) for v in q),1) if s == rep(s))
        check(len(support) == len(coeff), 'hyperplane witness arity')
        Rs = ([LO[dot(u,s)] for s in support] for u in product(E,repeat=4))
        check_fourier(coeff, 10**6, Rs, Fraction(3057,500))
    check(seen == good, 'all hyperplane labels')


def main():
    data = loads(Path(__file__).with_name('c7_rank_five_residual_fiber_certificate.json').read_text())
    check_thresholds()
    verify_projected_plane()
    verify_projected_line()
    check_rank_four(data['hyperplanes'])
    print('PASS projected fibers (118755 normalized plane cases, 72 in one class); rank-four bound 8 with two possible quotient forms', flush=True)
    check_rank_three(data['rank_three'])
    print('PASS rank-three bound 5: 140050 exact quotient cases, 1498 rational Fourier witnesses', flush=True)


if __name__ == '__main__':
    main()
