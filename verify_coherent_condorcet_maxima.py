#!/usr/bin/env python3
"""Exact coherent Condorcet-domain search for one through nine alternatives."""
from itertools import combinations, permutations
from math import comb
from sys import argv

EXPECTED = (None, 1, 2, 4, 9, 19, 43, 94, 211, 465)
WITNESS9 = (0,0,2,4,10,42,106,0,1,2,5,21,53,1,1,3,5,21,
            0,1,5,13,1,1,5,1,3,1)


def avoiding(n):
    """Insert the largest only before an increasing suffix."""
    if n == 0:
        return [()]
    out = []
    for p in avoiding(n - 1):
        start = max((i + 1 for i in range(len(p) - 1) if p[i] > p[i + 1]),
                    default=0)
        out.extend(p[:i] + (n - 1,) + p[i:] for i in range(start, len(p) + 1))
    return out


def inv_pos(p):
    pos = [0] * len(p)
    for i, a in enumerate(p):
        pos[a] = i
    return pos


def avoiding_direct(n):
    """Independent generator for exhaustive audit, not needed by default."""
    triples = list(combinations(range(n), 3))
    out = []
    for p in permutations(range(n)):
        q = inv_pos(p)
        if not any(q[c] < q[b] < q[a] for a,b,c in triples):
            out.append(p)
    return out


def packets(n, P):
    pairs = [(a,c) for a,c in combinations(range(n), 2) if c > a + 1]
    parts = [{} for _ in pairs]
    for i, p in enumerate(P):
        q = inv_pos(p)
        bit = 1 << i
        for (a,c), M in zip(pairs, parts):
            if q[c] < q[a]:
                key = sum(1 << (b - a - 1) for b in range(a + 1, c) if q[b] < q[c])
                M[key] = M.get(key,0) | bit
    return pairs, parts


def solve(n, all_ties, direct=False):
    P = avoiding_direct(n) if direct else avoiding(n)
    assert len(P) == len(set(P)) == comb(2*n,n)//(n+1)
    pairs, packets_by_style = packets(n, P)
    groups = [tuple(M.values()) for M in packets_by_style]
    packet_masks = [sum(g) for g in groups]  # groups inside a packet are disjoint
    full = (1 << len(P)) - 1

    # Warm start with a real, explicitly checked family: chose 1N3 or 3N1
    # according to the middle alternative's membership in a subset.
    best, witness, ties = 0, 0, set()
    for bset in range(1 << max(0,n-2)):
        S = full
        for (a,c), M, U in zip(pairs, packets_by_style, packet_masks):
            style = sum(1 << (b-a-1) for b in range(a+1,c) if not (bset >> (b-1)) & 1)
            S &= ~(U ^ M.get(style,0))
        score = S.bit_count()
        if score > best:
            best, witness = score, S

    seen = set()
    nodes = 0

    def reject(upper_bound):
        return upper_bound < best if all_ties else upper_bound <= best

    def visit(S):
        nonlocal best, witness, nodes
        nodes += 1
        size = S.bit_count()
        if reject(size) or S in seen:
            return
        seen.add(S)
        active = []
        for i, packet in enumerate(packet_masks):
            U = S & packet
            total = U.bit_count()
            if total <= 1:
                continue
            partial = [(m,(S&m).bit_count()) for m in groups[i]]
            partial = [(m,z) for m,z in partial if z]
            if len(partial) < 2:
                continue
            loss = total - max(z for m,z in partial)
            if reject(size - loss):
                return
            active.append((loss,U,total,partial))
        if not active:
            if size > best:
                best, witness = size, S
                ties.clear()
            if all_ties:
                ties.add(S)
            return
        active.sort(key=lambda row: row[0], reverse=True)

        # Partition portions of S greedily into disjoint packet pieces.
        # Every portion allows at most its largest style subgroup.
        rest, upper = S, size
        for loss,U,total,partial in active:
            Q = rest & U
            if Q == U:
                upper -= loss
            elif Q:
                upper -= Q.bit_count() - max((Q&m).bit_count() for m,z in partial)
            if reject(upper):
                return
            rest ^= Q

        # Choose one conflicting pair. Every coherent domain extends one
        # of these style branches, including if it contains no inversions of it.
        loss,U,total,partial = min(
            active, key=lambda row: (sum(not reject(size-row[2]+z) for m,z in row[3]),
                                     -row[0]))
        outside = S ^ U
        for m,z in sorted(partial, key=lambda entry: -entry[1]):
            if reject(size - total + z):
                break
            visit(outside | (S & m))

    visit(full)
    selected = ties if all_ties else {witness}
    assert selected and all(S.bit_count() == best for S in selected)
    data = [frozenset(p for i,p in enumerate(P) if S>>i&1) for S in selected]
    return best, data, nodes


def restrict_patterns(D, T):
    T = frozenset(T)
    return {tuple(a for a in p if a in T) for p in D}


def check_coherent(D, n, copious=False):
    for a,b,c in combinations(range(n), 3):
        R = restrict_patterns(D, (a,b,c))
        assert all(p[-1] != a for p in R) or all(p[0] != c for p in R)
        if copious:
            assert len(R) == 4


def decode_witness9():
    pairs = [(a,c) for a,c in combinations(range(9),2) if c > a + 1]
    style = dict(zip(pairs, WITNESS9))
    triples = list(combinations(range(9),3))
    assert len(style) == len(pairs) == len(WITNESS9)
    D = set()
    # Independent direct check of the concrete witness: test the actual
    # never-position conditions for all 9! permutations.
    for p in permutations(range(9)):
        q = inv_pos(p)
        for a,b,c in triples:
            flag = (style[a,c] >> (b - a - 1)) & 1
            bad = (q[c] < min(q[a],q[b])) if flag else (q[a] > max(q[b],q[c]))
            if bad:
                break
        else:
            D.add(p)
    return frozenset(D)


def normal_forms(D):
    """Every relabelling of D whose image contains the increasing order."""
    for p in D:
        relabel = inv_pos(p)
        yield tuple(sorted(tuple(relabel[a] for a in q) for q in D))


def check_isomorphism(Ds):
    groups = {}
    for D in Ds:
        L = list(normal_forms(D))
        assert sum(U == tuple(sorted(D)) for U in L) == 1
        groups.setdefault(min(L), []).append(D)
    assert sorted(map(len,groups.values())) == [4,4,4,4]
    # Ordinary isomorphism does not include reversal of the ranking order.
    paired = []
    for C, G in groups.items():
        dual_key = min(normal_forms(frozenset(p[::-1] for p in G[0])))
        assert dual_key in groups
        paired.append(dual_key != C)
    print('axis-labelled optimizers:',len(Ds),'; ordinary classes:',len(groups),
          '; non-self-dual classes:',sum(paired),flush=True)
    return sum(paired)


def main():
    direct = '--direct' in argv
    orders = [int(a) for a in argv[1:] if a != '--direct'] or list(range(1,10))
    for n in orders:
        assert 1 <= n <= 9
        maximum, Ds, nodes = solve(n, n == 9, direct)
        assert maximum == EXPECTED[n]
        for D in Ds:
            check_coherent(D,n,n == 9)
        print('PASS',n,maximum,nodes,flush=True)
        if n == 9:
            assert len(Ds) == 16 and decode_witness9() in Ds
            assert check_isomorphism(Ds) == 4
            P = avoiding(4)
            _, masks = packets(4, P)
            nontrivial = 0
            for M in masks:
                nontrivial |= sum(M.values())
            F = [p for i,p in enumerate(P) if not (nontrivial >> i) & 1]
            assert restrict_patterns(F,(0,2,3)) == {(0,2,3),(0,3,2)}


if __name__ == '__main__':
    main()
