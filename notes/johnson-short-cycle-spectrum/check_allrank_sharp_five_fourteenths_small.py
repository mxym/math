#!/usr/bin/env python3
"""SECOND RATIONAL DUAL CERTIFICATE: smaller denominator, 5/14 sharp.

Mathematical reduction (in ALL_RANK_SHARP_FIVE_FOURTEENTHS.md):
  For every g, Q_g(z)=prod_cycle(1+z^length) is in the linear span of
  all subset-image marginal indicators. At q in (0,1) put
    U_q(g)=prod_cycle(q^length+(1-q)^length).
  Thus Phi(g)=sum_i alpha_i*(1-U_{q_i}(g)) is an admissible
  dual perturbation. This checker proves for EVERY nonidentity
  permutation of EVERY degree:
       9/14 <= Phi(g) <= 1.

For moved point count 2..43 it checks EVERY partition with parts>=2 using
ONLY exact integer products and comparisons. For >=44 it checks an exact
rational tail inequality and the analytic power-mean inequality stated
in the paper handles ALL unbounded cycles. No LP solver, floating point,
randomness, or external package. Explicit exceptions, not disabled asserts.

Run from any directory:
  python3 check_allrank_sharp_five_fourteenths_small.py
"""

from fractions import Fraction
from math import lcm

# Five evaluation parameters and rational weights. Values are literal,
# independently specified certificate inputs, NOT read from a solver.
Q = ((1, 2), (1, 3), (1, 4), (1, 5), (1, 6))
DENOM = 30_625
WEIGHTS = (
    4_036_494,
    -10_841_250,
    13_334_928,
    -8_850_625,
    2_344_953,
)
MAX_MOVED = 43
TAIL_HALF_EXPONENT = 22


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def polynomial_cycle_product(partition, q):
    """Returns the exact rational product U_q for listed nontrivial cycles."""
    out = Fraction(1)
    for length in partition:
        out *= q ** length + (1 - q) ** length
    return out


def check_contacts():
    weights = [Fraction(w, DENOM) for w in WEIGHTS]
    params = [Fraction(a, b) for a, b in Q]
    require(sum(weights) == Fraction(4, 5), "weight-sum contact")
    expected = { (2,): Fraction(9, 14), (4,): Fraction(1),
                 (3, 3): Fraction(9, 14) }
    for cycles, target in expected.items():
        phi = sum((w * (1 - polynomial_cycle_product(cycles, q))
                   for w, q in zip(weights, params)), Fraction(0))
        require(phi == target, f"contact {cycles}: {phi} != {target}")
    require(all(p >= 1 and 0 < a < b for a, b in Q for p in (a,)),
            "invalid q")
    return params, weights


def check_finite():
    """Enumerate all nontrivial partitions into cycles>=2 through 43.

    Fixed points have U_q-factor q+(1-q)=1, so there is no dependence
    on their count; this is exhaustively ALL nonidentity conjugacy
    classes with at most 43 moved vertices, in any symmetric group.
    """
    common = lcm(*(b for _, b in Q))
    require(common == 60, "unexpected common denominator")
    factors = [
        [0, 0] + [
            a ** ell + (b - a) ** ell for ell in range(2, MAX_MOVED + 1)
        ]
        for a, b in Q
    ]
    multiply = [common // b for _, b in Q]
    powers = [[pow(v, m) for m in range(MAX_MOVED + 1)]
              for v in multiply]
    totals = [pow(common, m) for m in range(MAX_MOVED + 1)]
    count = 0
    global_min = None
    global_max = None
    min_witness = None
    max_witness = None
    lower_contacts = []
    upper_contacts = []

    def check(cycles, m, products):
        nonlocal count, global_min, global_max, min_witness, max_witness
        count += 1
        base = totals[m]
        numerator = sum(
            w * (base - prod * powers[i][m])
            for i, (w, prod) in enumerate(zip(WEIGHTS, products))
        )
        denominator = DENOM * base
        # Compare without rounding ANY intermediate number.
        require(14 * numerator >= 9 * denominator,
                f"lower bound failed on {cycles}")
        require(numerator <= denominator,
                f"upper bound failed on {cycles}")
        if 14 * numerator == 9 * denominator:
            lower_contacts.append(tuple(cycles))
        if numerator == denominator:
            upper_contacts.append(tuple(cycles))
        value = Fraction(numerator, denominator)
        if global_min is None or value < global_min:
            global_min, min_witness = value, tuple(cycles)
        if global_max is None or value > global_max:
            global_max, max_witness = value, tuple(cycles)

    def recurse(remainder, largest, moved, products, cycles):
        if remainder == 0:
            check(cycles, moved, products)
            return
        for ell in range(min(remainder, largest), 1, -1):
            recurse(
                remainder - ell,
                ell, moved + ell,
                [products[i] * factors[i][ell] for i in range(len(Q))],
                cycles + (ell,),
            )

    for moved in range(2, MAX_MOVED + 1):
        recurse(moved, moved, 0, [1] * len(Q), ())

    require(global_min == Fraction(9, 14), "minimum contact not attained")
    require(global_max == Fraction(1), "maximum contact not attained")
    require(count == 63260, "partition enumeration incomplete")
    require(set(lower_contacts) == {(2,), (3, 3)}
            and len(lower_contacts) == 2, "wrong lower-contact classification")
    require(upper_contacts == [(4,)], "wrong upper-contact classification")
    return count, global_min, min_witness, global_max, max_witness


def check_tail(params, weights):
    """Prove all moved counts  >= 44 by one exact rational inequality.

    For ell>=2:
      q^ell + (1-q)^ell <= (q^2 + (1-q)^2)^(ell/2).
    Hence product over cycles with M moved vertices is <= rho^(M/2),
    and <= rho^22 if M>=44. It follows that
      |Phi(g)-4/5| <= sum_i |alpha_i| rho_i^21.
    """
    bound = sum((
        abs(w) * (q * q + (1 - q) * (1 - q)) ** TAIL_HALF_EXPONENT
        for w, q in zip(weights, params)
    ), Fraction(0))
    require(bound < Fraction(7, 50),
            "strong rational tail bound must be below 7/50")
    require(bound < Fraction(11, 70),
            "tail bound does not reach lower margin")
    require(bound < Fraction(1, 5),
            "tail bound does not reach upper margin")
    return bound


def main():
    require(MAX_MOVED + 1 == 2 * TAIL_HALF_EXPONENT,
            "finite-tail split is not logically exhaustive")
    params, weights = check_contacts()
    count, small, amin, large, amax = check_finite()
    tail = check_tail(params, weights)
    print("EXACT CONTACTS: Phi(2)=Phi(3,3)=9/14; Phi(4)=1.")
    print("RATIONAL INPUT DENOMINATOR:", DENOM)
    print("FINITE PARTITIONS (all cycle lengths >=2, moved<=43):", count)
    print("EXACT GLOBAL FINITE MINIMUM:", str(small), "at", amin)
    print("EXACT GLOBAL FINITE MAXIMUM:", str(large), "at", amax)
    print("UNBOUNDED TAIL: sum |weight| rho^22 < 7/50:",
          tail < Fraction(7, 50))
    print("TAIL VALUE (exact rational):", tail)
    print("ALL-RANK 5/14 UNIVERSAL DUAL CERTIFICATE PASS.")


if __name__ == "__main__":
    main()
