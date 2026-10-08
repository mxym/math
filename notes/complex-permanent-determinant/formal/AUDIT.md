# Lean proof and semantic fidelity audit

## What is completely kernel-verified: Theorems 1A and 1B

The endpoint
ComplexPencilMain.sharp_complex_lens_iff
is a universally quantified equivalence over the original complex
coefficient and all nine complex entries. The determinant and
permanent are defined by their usual 3-by-3 signed and unsigned
six-term expansions. The squared complex norm used is Re(z)^2+Im(z)^2,
and each rowSq equals its Euclidean squared norm.

The endpoint includes ALL matrices (including zeros), complex
coefficients inside and on the full closed coefficient lens, and
also proves the reverse direction outside that lens.

The separate theorem
ComplexPencilMain.coefficient_four_thirds_is_sharp
quantifies over all candidate real squared-norm constants B, proves
B >= 4/3 whenever the inequality holds for all complex matrices,
and supplies the explicit all-ones witness.

## Full complex pencil minimax: added verified dependencies

9. `NormCurve.normBoundSq` is the maximum of five explicit real
   squared-norm candidate values for arbitrary complex coefficients.
   The `bound_preconditions` proof formally derives all sign and
   determinant discriminant conditions, including Fourier offsets,
   from this maximum. It therefore feeds the previously verified
   universal Hermitian positive semidefinite result with **no lens
   restriction**.
10. `Witnesses.omega_sq`, `omegaBar_sq`, `per_fourier`,
    `det_fourier`, `fourier_minus_exact` and
    `fourier_plus_exact` provide precise non-real complex extremizers
    with squared row norm product 27. They prove the two additional
    lower bounds (imaginary Fourier extrema); the parity and all-ones
    witnesses prove the other three.
11. `ExactNorm.sharp_full_pencil_norm_iff` is the complete
    squared-constant minimax equivalence:
    for *every* complex coefficient and real B, the full inequality
    holds for *all* complex matrices if and only if
    B is at least the explicit five-branch candidate maximum.
    No matrix regularity, nonzero-row assumption or optimizer
    assumption is inserted in the theorem.
12. Its actual `#print axioms` output lists only the standard
    three Lean axioms; no `sorryAx` is present. The complete complex
    norm result thus has a kernel-checked proof rather than
    a finite sample certificate.

## Proven dependency chain

1. Symbolic determinant and principal minor expansions exactly match
   the repository 4096-node rational certificate, but here are proved
   for all REAL variables using Lean ring normalization.
2. Nonnegative symmetric cubics are represented explicitly as sums
   of nonnegative squared differences.
3. A separately proved complex Hermitian 3x3 principal minor criterion
   converts seven nonnegative minors into positivity of the ACTUAL
   complex quadratic form, with all singular-pivot cases covered.
4. A generic three-coordinate operator identity converts the
   square of the concrete lambda-dependent matrix action to the
   Hermitian quadratic form. The three-vector complex Cauchy–Schwarz
   identity is proved from a positive Lagrange square decomposition.
5. Exact conjugate phase and squared modulus identities prove that
   the true 3-by-3 Hermitian determinant and minors are the same as
   the positive six-variable polynomial certificates.
6. The coefficient lens q+2|x|<=1/3 discharges every sign condition,
   including 3B-4 and the nonnegative quadratic discriminant.
7. Identity and odd permutation matrices establish necessity.
8. The all-ones matrix forces the sharp 4/3 squared coefficient.

These are all actual kernel-checkable Lean declarations, not
finite examples, numerical optimization, or imported assumptions
equivalent to the desired theorem.

## Trust boundary

Official Lean compiler and kernel, official pinned Mathlib, and
three Lean standard axioms:
  propext, Classical.choice, Quot.sound

The five built-in axiom reports in Main.log confirm these are the
only axioms used in the checked endpoints and core algebraic lemmas.
There are no user-provided axioms, sorry, admit or native_decide in
the proof source. All source hashes and logs are independently
replayable.

Theorem 1B now **is** fully kernel-verified by the three additional
modules and its five sharp witnesses. Theorem 2 (complete equality
classification for the absolute-value endpoint) and finite-dimensional
tensorization remain **outside the formalization scope**. They must not
be represented as Lean-proven until separately completed.
