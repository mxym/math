# Lean proof and semantic fidelity audit

## What is completely kernel-verified

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

The complete five-term coefficient-dependent norm outside the lens
(Theorem 1B), and equality classifications (Theorem 2), are NOT
covered by this endpoint. They must not be represented as formally
verified until their actual mathematical statements are proved in
Lean with the required witnesses.
