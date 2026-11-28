#!/usr/bin/env python3
"""Replay the exact divisibility logic isolated in PROOF.md."""

from math import prod


def printed_alg_guard(q, determinants):
    return all(d % q == 0 for d in determinants)


def repaired_alg_guard(q, determinants):
    return all(d % q != 0 for d in determinants)


def lemma_44_hypothesis(q, determinants):
    return prod(determinants) % q != 0


def main():
    # r=2 has one nonzero ancestor determinant.
    q = 5
    printed_example = [10]
    good_example = [11]

    assert printed_alg_guard(q, printed_example)
    assert not lemma_44_hypothesis(q, printed_example)

    assert not printed_alg_guard(q, good_example)
    assert repaired_alg_guard(q, good_example)
    assert lemma_44_hypothesis(q, good_example)

    # For nonzero products, the repaired guard is exactly q ∤ R_anc.
    samples = [
        [1],
        [4, 6],
        [11, 16, 26],
        [10],
        [10, 11],
        [15, 25, 35],
    ]
    for ds in samples:
        assert repaired_alg_guard(q, ds) == lemma_44_hypothesis(q, ds)
        assert not (
            printed_alg_guard(q, ds) and lemma_44_hypothesis(q, ds)
        )

    print("q=5")
    print("printed_guard_example=10")
    print("printed_guard_accepts=True")
    print("lemma_4_4_hypothesis_on_printed_example=False")
    print("repaired_guard_example=11")
    print("repaired_guard_accepts=True")
    print("lemma_4_4_hypothesis_on_repaired_example=True")
    print("repaired_guard_equals_lemma_hypothesis_on_samples=True")
    print("printed_guard_and_lemma_hypothesis_disjoint_on_samples=True")


if __name__ == "__main__":
    main()
