#!/usr/bin/env python3
"""Independent exhaustive n=5 support partition and polar-rank audit."""
from collections import Counter
from itertools import combinations

N = 32
all_points = tuple(range(N))
valid_lines = tuple((1 << a) | (1 << b) | (1 << (a ^ b))
                    for a, b in combinations(range(1, N), 2) if b < (a ^ b))
monomials = tuple(1 << i for i in range(5)) + tuple((1 << i) | (1 << j)
                                                   for i, j in combinations(range(5), 2))
monomial_tables = tuple(sum(1 << x for x in all_points if x & m == m) for m in monomials)
FULL = (1 << N) - 1
assert len(valid_lines) == len(set(valid_lines)) == 155
assert len(monomial_tables) == 15


def rank_of_polar(coeff):
    # Coefficients of q(x+y)+q(x)+q(y)+q(0) against y=e_i.
    radical = 0
    for x in all_points:
        covector = 0
        for k, (i, j) in enumerate(combinations(range(5), 2), 5):
            if coeff & (1 << k):
                covector ^= (((x >> i) & 1) << j) ^ (((x >> j) & 1) << i)
        radical += covector == 0
    assert radical in (2, 8, 32)
    return 5 - (radical.bit_length()-1)


def exact_cover(S):
    allowed = tuple(L for L in valid_lines if L & S == L)
    by_vertex = {}
    for L in allowed:
        x = L
        while x:
            bit = x & -x
            by_vertex.setdefault(bit, []).append(L)
            x ^= bit

    def search(remaining):
        if remaining == 0:
            return True
        x = remaining
        best = None
        while x:
            bit = x & -x
            x ^= bit
            avail = tuple(L for L in by_vertex.get(bit, ()) if L & remaining == L)
            if not avail:
                return False
            if best is None or len(avail) < len(best):
                best = avail
        return any(search(remaining ^ L) for L in best)

    return search(S)


def main():
    rank_counts, cover_counts = Counter(), Counter()
    for coeff in range(1 << 15):
        f = FULL  # constant term is 1, so 0 lies in the support.
        c = coeff
        while c:
            bit = c & -c
            f ^= monomial_tables[bit.bit_length()-1]
            c ^= bit
        if f.bit_count() == 16:
            rank = rank_of_polar(coeff)
            rank_counts[rank] += 1
            if exact_cover(f ^ 1):
                cover_counts[rank] += 1
    assert rank_counts == {0:31, 2:4340, 4:13888}
    assert cover_counts == {0:31, 4:13888}
    print("n=5: all 32768 normalized quadratic indicators; 155 different lines")
    print("balanced by polar rank 0,2,4:", *(rank_counts[r] for r in (0,2,4)))
    print("admit exact 2-plane partition by polar rank 0,2,4:",
          *(cover_counts[r] for r in (0,2,4)))
    print("coordinate-labelled supports meeting all hypotheses and parity:", sum(cover_counts.values()))


if __name__ == "__main__":
    main()
