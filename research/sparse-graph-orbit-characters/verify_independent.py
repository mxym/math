#!/usr/bin/env python3
"""Independent GF(2) orbit-span closure under adjacent transpositions."""
from itertools import combinations, permutations
from random import Random


def push(basis, x):
    while x:
        k = x.bit_length()-1
        if k not in basis:
            basis[k] = x
            return x
        x ^= basis[k]
    return 0


def identify(n):
    E = list(combinations(range(n),2))
    pos = {e:k for k,e in enumerate(E)}
    full = (1<<len(E))-1
    swaps = []
    for j in range(n-1):
        pairs = []
        for i in range(n):
            if i not in (j,j+1):
                a,b = sorted((pos[tuple(sorted((j,i)))],pos[tuple(sorted((j+1,i)))]))
                pairs.append((a,b))
        swaps.append(pairs)

    def moved(g,pairs):
        d = 0
        for a,b in pairs:
            if ((g>>a)^(g>>b))&1:
                d ^= (1<<a)|(1<<b)
        return g ^ d

    def orbit_span(g):
        B,q = {},[]
        for tr in swaps:
            v = push(B,g^moved(g,tr))
            if v:
                q.append(v)
        idx = 0
        while idx < len(q):
            x = q[idx]
            idx += 1
            for tr in swaps:
                v = push(B,moved(x,tr))
                if v:
                    q.append(v)
        return B

    def cut(u):
        return sum(1<<k for k,(i,j) in enumerate(E) if ((u>>i)^(u>>j))&1)

    def boundary(g):
        D = 0
        for k,(i,j) in enumerate(E):
            if (g>>k)&1:
                D ^= (1<<i)|(1<<j)
        return D

    def cut_plus_constant(g):
        # Solve for u with u_0=0, for each of the two constants.
        for c in (0,1):
            u = sum((((g>>pos[(0,j)])&1)^c)<<j for j in range(1,n))
            if cut(u)^(full if c else 0)==g:
                return True
        return False

    def check(g):
        B = orbit_span(g)
        if g in (0,full):
            assert not B
            return 0
        if cut_plus_constant(g):
            expected = {}
            for j in range(1,n):
                push(expected,cut(1|(1<<j)))
            for q in B.values():
                assert not push(dict(expected),q)
            assert len(B)==len(expected)==n-1-(n%2==0)
            return 1
        if boundary(g) in (0,(1<<n)-1):
            assert len(B)==len(E)-n
            assert all(boundary(x)==0 and x.bit_count()%2==0 for x in B.values())
            return 2
        assert len(B)==len(E)-1
        assert all(x.bit_count()%2==0 for x in B.values())
        return 3

    return check, cut, E, full


def main():
    totals = []
    for n in (4,5,6):
        check,_,E,full = identify(n)
        by_class = [0]*4
        for g in range(full+1):
            by_class[check(g)] += 1
        M = len(E)
        expected_extra = ((1 << (M-n+2)) if n%2==0
                          else (1 << (M-n+1)) + (1<<n)-2)
        assert sum(by_class[:3]) == expected_extra
        totals.append(tuple(by_class))
    print(f'PASS independent n=4..6 full GF(2) orbit spans, four-way class counts: {totals}')
    R = Random(84)
    samples = total = 0
    for n in (7,8,9,12):
        check,cut,E,full = identify(n)
        examples = [0,full,cut(1),cut(1)^full]
        x = sum(1<<j for j,(a,b) in enumerate(E) if a<3 and b<3)
        examples += [x,1]
        assert [check(g) for g in examples] == [0,0,1,1,2,3]
        for _ in range(36):
            g = R.getrandbits(len(E))
            check(g)
            samples += 1
        total += len(examples)
    print(f'PASS larger GF(2) cases: {samples} random graphs and {total} branch witnesses')

    # Vertex relabeling preserves triangle form; an edge permutation does not.
    E = list(combinations(range(4),2))
    a = {(0,1),(0,2),(1,2)}
    def sign(b):
        return (-1)**len(a ^ (a & b))
    vals = [sign({tuple(sorted((p[i],p[j]))) for i,j in a})
            for p in permutations(range(4))]
    arbitrary = [sign(set(b)) for b in combinations(E,3)]
    assert sum(vals)==24 and sum(arbitrary)==0
    print('PASS action control: vertex relabeling and arbitrary edge permutations differ')


if __name__ == '__main__':
    main()
