# 010 v1

## Main result

For every epsilon > 0, finite m >= 1, and 1 < beta < 3/2, and for arbitrary
lower bounds on m integer scales, there is one complete smooth metric g on
R^3 such that:

- g is Euclidean near the origin;
- Ric_g >= 0 and Ric_g > 0 outside a compact set;
- the identity is globally (1+epsilon)-bi-Lipschitz to Euclidean space;
- at m arbitrarily separated starting degrees k_r, the same g violates
  Euclidean harmonic-dimension comparison at every integer degree from
  k_r through floor(beta(k_r+1))-1.

The asymptotic volume ratio may be taken arbitrarily close to one.

## Files

- paper.md — complete theorem and proof.
- DEPENDENCIES.md — pinned upstream commit and exact imported lemmas.
- PROOF_AUDIT.md — independent dependency-by-dependency proof audit.
- verification/check_bands.py — exact integer/rational parameter replay.
- verification/run.txt — recorded checker output.

## Verification

Run:

    python3 verification/check_bands.py

The checker uses Python integers and fractions.Fraction only. It verifies
a five-band concrete instance of the finite arithmetic conditions:
band separation, strict mean-frequency margin, low-rank margin, block
containment, and final dimension inequality.

The checker intentionally does not certify the imported analytic existence
theorem. Those dependencies are pinned and audited separately.

## Status and scope

The proof uses no floating-point calculation, heuristic optimization, or
unverifiable solver output.

The remaining high-value question is the genuinely countable quantifier
reversal: whether a single complete Ricci-nonnegative metric can violate
integer-degree harmonic dimension comparison at infinitely many unbounded
degrees.

No literature-priority claim is made in v1.
