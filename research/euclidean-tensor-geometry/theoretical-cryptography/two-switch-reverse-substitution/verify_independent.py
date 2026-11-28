#!/usr/bin/env python3
"""Independent linear-algebra checks of endpoint attainability and the cited sharp convec."""
from fractions import Fraction


def rank(matrix, q):
    if not matrix:
        return 0
    a = [list(v) for v in matrix]
    r = 0
    for j in range(len(a[0])):
        t = next((i for i in range(r,len(a)) if a[i][j] % q), None)
        if t is None:
            continue
        a[r], a[t] = a[t], a[r]
        z = pow(a[r][j] % q, -1, q)
        a[r] = [(x * z) % q for x in a[r]]
        for i in range(r+1,len(a)):
            c = a[i][j]
            a[i] = [(x - c*y) % q for x,y in zip(a[i],a[r])]
        r += 1
    return r


def verify_scheme(shares, qs, minqual, sizes):
    masks = [sum(1 << i for i in t) for t in minqual]
    nt = 0
    w = len(next(iter(next(v for v in shares if v))))
    s = [1]+[0]*(w-1)
    for q in qs:
        assert [rank(v, q) for v in shares] == sizes
        for coal in range(1 << len(shares)):
            rows = [row for i, ss in enumerate(shares) if coal >> i & 1 for row in ss]
            a, b = rank(rows,q), rank(rows+[s],q)
            assert (a==b) == any(c & coal == c for c in masks)
            if a!=b:
                # Given any secret, outputs form the same integer-count
                # law on the image of the tape matrix iff removing s's
                # coordinate does not drop rank of the rows.
                assert a == rank([r[1:] for r in rows],q)
            nt += 1
    return nt


def shares_for_linear_components(components):
    # Components use the same scalar secret but disjoint tape coordinates.
    d = 1 + sum(mx for mx,_ in components)
    out = [[] for _ in range(4)]
    k = 1
    for w,L in components:
        for i, recv in enumerate(L):
            for v in recv:
                assert len(v) == w+1
                out[i].append([v[0]]+[0]*(k-1)+list(v[1:])+[0]*(d-k-w))
        k += w
    return out


def star(center, leaves):
    return (1,[[(0,1)] if i==center else [(1,-1)] if i in leaves else [] for i in range(1,5)])


def sh_points(points,w):
    return (w,[[tuple(a**d for d in range(w+1)) for a in T] for T in points])


def ends():
    three = (2,[[(0,1,0)],[],[(0,0,1)],[(1,-1,-1)]])
    m = (1,[[],[(1,1)],[(1,2)],[(1,3)]])
    row = [
      (((1,2),(2,3),(3,4)),
       [(star(2,{1,3}),star(3,{4})),(star(3,{2,4}),star(2,{1}))],
       [(1,1,2,1),(1,2,1,1)]),
      (((1,2),(2,3),(2,4),(3,4)),
       [(m,star(2,{1})),(star(2,{1,3,4}),star(3,{4}))],
       [(1,2,1,1),(1,1,2,2)]),
      (((1,2),(2,3),(1,3,4)),
       [(sh_points(((3,),(1,2),(4,),(1,)),2),),(star(2,{1,3}),three)],
       [(1,2,1,1),(2,1,2,1)]),
      (((1,2),(2,3),(2,4),(1,3,4)),
       [(sh_points(((3,),(1,2),(4,),(5,)),2),),(star(2,{1,3,4}),three)],
       [(1,2,1,1),(2,1,2,2)]),
    ]
    out=0
    for bases, two, dims in row:
        tests = [tuple(x-1 for x in t) for t in bases]
        for comp, expected in zip(two,dims):
            s=shares_for_linear_components(comp)
            out += verify_scheme(s,(7,11),tests,list(expected))
    return out


def enc_sharp():
    # Khazaei Appendix B.2: s=coordinate 0; primary masks 1..4;
    # secondary masks 5..8. The anchor is included here and then dropped.
    forms = [
        [(1,), (4,), (0,1,2,3)], [(0,1)], [(2,)], [(1,), (3,)],
        [(5,), (6,), (7,)], [(1,6,7), (1,3,5,6,4)],
        [(6,7), (1,5,6,4), (1,3,5,8)], [(4,), (8,)],
    ]
    s = [[[int(i in row) for i in range(9)] for row in p] for p in forms]
    bases = [(0,1)]
    for R in [(1,),(0,2)]:
        for Q in [(3,),(4,5),(5,6),(4,6,7)]:
            bases.append(tuple(sorted(R+Q)))
    sizes = [3,1,1,2,3,2,3,2]
    qs = (2,3,5,7,11)
    a = verify_scheme(s,qs,bases,sizes)
    def new_id(i):
        assert i != 3
        return i-int(i>3)
    a += verify_scheme(s[:3]+s[4:],qs,
                       [tuple(new_id(i) for i in b) for b in bases if 3 not in b],
                       sizes[:3]+sizes[4:])
    return a


def factor_check():
    # Explicit rational reverse factors and obstruction at the next grid point.
    # An 8/9 realization is found without calling the closed-form formula, by
    # checking mixture weights of the two endpoint convecs for each factor.
    A, B = ((1,2,1,1),(2,1,2,1))
    c_outer,c_inner = (3,1,1),(3,2,3,2)
    best = 0
    for r in (Fraction(8,9),Fraction(9,10),Fraction(1)):
        exists = False
        for num_x in range(41):
            tx = Fraction(num_x,40)
            x = [tx*a+(1-tx)*b for a,b in zip(A,B)]
            if any(r*x[j] > c for j,c in zip((0,1,3),c_outer)):
                continue
            for num_y in range(41):
                ty = Fraction(num_y,40)
                y = [ty*a+(1-ty)*b for a,b in zip(A,B)]
                if all(r*x[2]*a<=b for a,b in zip(y,c_inner)):
                    exists = True
        assert exists == (r == Fraction(8,9))
        if exists:
            best = r
    # Necessary half-space bound without discretizing either capacity.
    assert best == (c_outer[1]+Fraction(c_inner[1]+c_inner[2],3))/3 == Fraction(8,9)
    return best


if __name__ == '__main__':
    print(f"PASS endpoint schemes: {ends()} finite-field coalition checks")
    print(f"PASS Khazaei sharp point with/without anchor: {enc_sharp()} coalition checks; factor {factor_check()}")
