#!/usr/bin/env python3
"""Exact auxiliary checks for the nine-point ternary rigidity note."""

from itertools import combinations, product
from math import prod

F = (0, 1, 2)


def insist(cond, detail):
    if not cond:
        raise RuntimeError(detail)


def balanced(word):
    w = tuple(word)
    return len(w) == 9 and all(w.count(a) == 3 for a in F)


def add(x, y, eps=1):
    return tuple((a + eps*b) % 3 for a, b in zip(x, y))


def word_check():
    # Constants added separately to the three words preserve all tests.
    # After zeroing their first entries, a coordinate permutation
    # preserving the first place puts the first word in canonical order.
    u = (0, 0, 0, 1, 1, 1, 2, 2, 2)
    words = [(0,)+w for w in product(F, repeat=8) if balanced((0,)+w)]
    bad = [v for v in words if balanced(add(u, v, -1))
           and not balanced(add(u, v))]
    tested = 0
    for v, w in combinations(bad, 2):
        tested += 1
        insist(not balanced(add(v, w, -1)) or balanced(add(v, w)),
                ("bad pair", v, w))
    insist((len(words), len(bad), tested) == (560, 55, 1485),
            "changed balance-check parameters")
    print(f"balanced words {len(words)}, test family {len(bad)}, pairs {tested}")


def example_checks():
    space = set(product(F, repeat=3))

    def zero(A):
        return {b for b in space if balanced(sum(x*y for x,y in zip(a,b)) % 3
                                             for a in A)}

    exact_one = ({(x,y,0) for x in F for y in (0,1)}
                 | {(0,0,1),(0,1,1),(1,2,1)})
    exact_three = ({(0,0,0),(1,0,0),(0,1,0)}
                   | {(x,x,1) for x in F}
                   | {(x,0,2) for x in F})
    exact_nine = {(x,y,0) for x,y in product(F, repeat=2)}
    sets = [exact_one, exact_three, exact_nine]
    insist(all(len(A) == 9 for A in sets), "bad set sizes")
    zeros = [zero(A) for A in sets]
    insist(zeros[0] == set() and zeros[1] == {(0,0,1),(0,0,2)}
           and len(zeros[2]) == 24, ("bad zero sets", zeros))
    insist({add(x, y, -1) for x in exact_three for y in exact_three} == space,
            "three-character example has a missing difference")
    print("zero-set sizes in F3^3:", [len(s) for s in zeros])


def prior_matrix_check():
    # A circulant representative from Egan-Flannery-O Cathain section 6.1.
    w = (0, 0, 0, 0, 1, 2, 0, 2, 1)
    v = [add(w[j:]+w[:j], w, -1) for j in (1, 3)]
    insist(all(balanced(z) for z in [*v, add(*v), add(*v, -1)]),
            "unexpected circulant representative")
    # Recheck the rank-four six-point affine-orbit count used in the appendix.
    insist(81*prod(81-3**j for j in range(4)) == 2_729_376*720,
            "bad affine-orbit count")
    print("circulant prior representative and orbit-count checks passed")


if __name__ == "__main__":
    word_check()
    example_checks()
    prior_matrix_check()
    print("PASS")
