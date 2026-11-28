#!/usr/bin/env python3
"""Exact symbolic Shannon certificates and primal access-structure witness checks."""
from collections import Counter
from itertools import permutations

ROWS_I = """S i jA
S i jka
S i Aa
S j ia
S ij k
S ijk ijA
S jkA jAB
S ijkA jkABa
S jkAB jABa
S ija iAa
M jka ijka
M jAa ijAa
S jAa ABa
S kABa ABab
S ijkABa kABab
M ABab ijkABab"""
ROWS_P = """S i jk
S i ja
S i kab
S j Aa
S k jA
S ijk jkA
S ijA jAB
S ijkA ijAa
M jAB ijAB
S ija jAa
S kAa Aab
S ikAa kABa
S ijkAa ikABa
M kABa ijkABa
S ikab kAab
M iAab ikAab
S iAab ABab
M ABab iABab"""


def qualified(labels, first):
    i, j, k = (x in labels for x in 'ijk')
    p0 = frozenset(labels & set('ab'))
    assert p0 in (frozenset(), frozenset('a'), frozenset('ab'))
    p = (j and k, j, j or k)[len(p0)]
    b0 = frozenset(labels & set('AB'))
    assert b0 in (frozenset(), frozenset('A'), frozenset('AB'))
    return (i and p, i if first == 'i' else p, i or p)[len(b0)]


def verify_certificate(rows, first):
    out = Counter()
    b = 0
    for line in rows.splitlines():
        t, u, v = line.split()
        u, v = frozenset(u), frozenset(v)
        qu, qv = qualified(u, first), qualified(v, first)
        if t == 'S':
            out[u] += 1
            out[v] += 1
            out[u & v] -= 1
            out[u | v] -= 1
            assert qualified(u | v, first) or not (qu or qv)
            b += int(qu and qv and not qualified(u & v, first))
        else:
            assert t == 'M' and u < v and (not qu or qv)
            out[v] += 1
            out[u] -= 1
            b += int(not qu and qv)
    out.pop(frozenset(), None)
    assert {''.join(x): y for x, y in out.items() if y} == {'i': 3, 'j': 1, 'k': 1}
    return len(rows.splitlines()), b


KNOWN = {
    'P4': ('12', '23', '34'),
    'paw': ('12', '23', '24', '34'),
    'C2': ('12', '23', '134'),
    'K3': ('12', '23', '24', '134'),
}
WITNESS = {
    'P4': (('2', '3', '1', '14'), ('3', '2', '4', '14')),
    'paw': (('2', '3', '1', '14'), ('2', '4', '1', '13')),
    'C2': (('2', '1', '3', '34'), ('2', '3', '1', '14')),
    'K3': (('2', '1', '3', '34'), ('2', '3', '1', '14'), ('2', '4', '1', '13')),
}


def canonical(f, n):
    return min(tuple(sorted(sum(1 << p[i] for i in range(n) if (m >> i) & 1)
                            for m in f)) for p in permutations(range(n)))


def mask(a):
    return sum(1 << (int(i)-1) for i in a)


def check_witnesses():
    hits = 0
    for name, gens in KNOWN.items():
        basis = tuple(map(mask, gens))
        for i, p, a, b in WITNESS[name]:
            i, p, a, b = map(mask, (i,p,a,b))
            assert a < b and a & b == a and not ((i|p) & b)
            for base, row in [(0, (0,0,0,1)), (a,(0,1,0,1)), (b,(0,1,1,1))]:
                assert tuple(int(any(e & (base|x) == e for e in basis))
                             for x in (0,i,p,i|p)) == row
                hits += 4
    return hits


def classification():
    # Stinson Table 1, restricted to four participants (numbers 5--18).
    table = (
        '12 23 34', '12 13 14', '12 14 23 34', '12 23 24 34',
        '12 13 14 23 24', '12 13 14 23 24 34', '123 14', '134 12 23',
        '134 12 23 24', '123 124', '124 134 23', '123 124 134',
        '123 124 134 234', '1234',
    )
    known = {canonical(tuple(map(mask, x.split())), 4) for x in table}
    assert len(known) == 14
    connected_lists = 0
    classes = set()
    for code in range(1 << 16):
        if code & 1:
            continue
        yes = {x for x in range(16) if (code >> x) & 1}
        if any(not {x|1<<i for i in range(4)} <= yes for x in yes):
            continue
        mins = [a for a in yes if all((a^(1<<i)) not in yes
                                     for i in range(4) if a>>i&1)]
        if not mins or any(x.bit_count() == 1 for x in mins):
            continue
        connected = True
        for q in range(1, 15):
            if (all((r&q) in (0,r) for r in mins)
                    and any(r&q for r in mins) and any(r&~q for r in mins)):
                connected = False
        if not connected or any(not any(r>>i&1 for r in mins) for i in range(4)):
            continue
        classes.add(canonical(mins, 4))
        connected_lists += 1
    assert classes == known
    return connected_lists, len(classes)


def run():
    n, b = verify_certificate(ROWS_I, 'i')
    m, a = verify_certificate(ROWS_P, 'p')
    assert (n,b,m,a) == (16,8,18,9)
    # The orientations are different: the 18-row template loses strict terms
    # on the i-first grid and therefore cannot certify 9 there.
    assert verify_certificate(ROWS_P, 'i')[1] < 9
    l, c = classification()
    print(f"PASS coefficient telescopes: {n}/{m} rows with sharp right sides {b}/{a}, orientation negative control")
    print(f"PASS scope: {check_witnesses()} witness truth entries; {l} labelled connected structures, {c} isomorphism types")


if __name__ == '__main__':
    run()
