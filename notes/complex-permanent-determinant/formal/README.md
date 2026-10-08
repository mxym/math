# Full Lean verification of the sharp complex permanent–determinant coefficient lens

**Status:** Complete Lean 4.34.1 / Mathlib proofs of Theorems **1A and 1B** from
the public complex three-row permanent–determinant manuscript.
Theorem 2 (the full equality classification) and tensorization corollaries are not yet fully Lean-formalized.

## Full theorem proved

For each complex coefficient lambda, the following are equivalent:

1. For every complex 3-by-3 matrix A,
   |per(A) + lambda * det(A)| <=
   (2/sqrt(3)) times the product of the three Euclidean row norms.
2. |lambda|^2 + 2 |Re lambda| <= 1/3.

The exact Lean endpoint is

    ComplexPencilMain.sharp_complex_lens_iff

It quantifies over lambda and nine arbitrary complex matrix entries.
The permanent and determinant use their six usual
unsigned/signed monomial expansions. The Lean theorem states the
mathematically equivalent SQUARED inequality: complex squared modulus
of the pencil at most (4/3) times the three row squared Euclidean norms.
It includes arbitrary zero rows and all boundary coefficients.

Sharpness is *also fully proved*: a second independent endpoint,

    ComplexPencilMain.coefficient_four_thirds_is_sharp

shows that every candidate squared-norm constant valid for all complex
matrices must be at least 4/3, by the all-ones matrix witness.
Thus 2/sqrt(3) is the optimal unsquared constant throughout the lens.

## Entire complex coefficient norm, formally proved

The additional kernel theorem `ComplexPencilFull.sharp_full_pencil_norm_iff`
proves for **every** complex `lambda` and **every** real proposed squared-norm constant `B`:

    [for all 3x3 complex A,
       |per(A) + lambda*det(A)|^2 <= B*product(row squared norms)]
             iff normBoundSq(lambda) <= B.

The quantity `normBoundSq` is explicitly the maximum of

    4/3,
    1+|lambda|^2 + 2 Re(lambda),
    1+|lambda|^2 - 2 Re(lambda),
    |lambda|^2 + 1/3 + (2/sqrt(3)) Im(lambda),
    |lambda|^2 + 1/3 - (2/sqrt(3)) Im(lambda).

It is therefore exactly the square of the five-term norm formula
from Theorem 1B. Two explicit Fourier matrices give the sharp
complex-imaginary endpoints; parity permutation matrices give the
real endpoints; the all-ones matrix gives the 4/3 endpoint.

This is a full universal-norm **minimax theorem**, not merely an
upper bound or finite symbolic interpolation.

## Kernel-checked proof

- HermitianCertificate.lean: real six-parameter determinant and
  principal minor identities, exact nonnegative cubic SOS and sign
  certificate; all symbolic variables are universally quantified.
- PSD3.lean: rigorous complex Hermitian 3x3 principal minor => quadratic
  form nonnegativity, including zero-pivot cases, established by a
  division-free Schur/Cholesky polynomial identity.
- Link.lean: actual complex 3-vector Cauchy–Schwarz from a universal
  Lagrange identity, plus generic zero-diagonal operator norm
  complement identity.
- Main.lean: original lambda-dependent matrix, phase and normSq
  identities, actual determinant/three minor matches, positivity,
  complete coefficient lens sufficiency AND necessity, sharp constant.
- NormCurve.lean: five candidate squared norms, exactly quantified
  parameter inequalities and upper certificate for all complex lambda.
- Witnesses.lean: explicit primitive-cube-root Fourier matrices,
  precise permanent/determinant evaluations and two optimal
  imaginary-direction squared-modulus witnesses.
- ExactNorm.lean: universal quantified five-branch minimax theorem
  with both upper and lower bounds, plus its Lean axiom audit.

No theorem assumes the missing endpoint as a hypothesis.
The boundary cases are covered by nonstrict polynomial inequalities.

## Reproduce with the pinned Lean compiler and Mathlib

Compiler: Lean 4.34.1, git 5045d0056413266e57c625dcd7c365b10e377c52.
Mathlib commit: d13f23b723b8a846827a245b89c10fc7d3f11612.
Use the included lean-toolchain and lake-manifest.json, without
substituting a newer Mathlib checkout.

From this directory, after fetching the pinned official Mathlib
cache using Lake:

    mkdir -p .lake/build/lib/lean
    lake env lean -o .lake/build/lib/lean/HermitianCertificate.olean HermitianCertificate.lean
    lake env lean -o .lake/build/lib/lean/PSD3.olean PSD3.lean
    lake env lean -o .lake/build/lib/lean/Link.olean Link.lean
    lake env lean -o .lake/build/lib/lean/Main.olean Main.lean
    lake env lean -o .lake/build/lib/lean/NormCurve.olean NormCurve.lean
    lake env lean -o .lake/build/lib/lean/Witnesses.olean Witnesses.lean
    lake env lean ExactNorm.lean
    sha256sum -c SHA256SUMS

The original true compiler outputs are included:
cert-build.log, psd-build.log, Link.log, Main.log.
In Main.log the built-in Lean axiom reports for the Theorem 1A endpoints
and three core dependencies list only
propext, Classical.choice and Quot.sound.
The `ExactNorm.log` audit of the Theorem 1B endpoint also lists only
these same standard axioms. No sorry, admit, native_decide, unsafe
or custom axiom appears in the owned proof files.

## Precise limitation

Complete for Theorem 1A (complex sharp coefficient-lens equivalence)
and Theorem 1B (five-branch exact coefficient-dependent operator norm),
including all five optimality witnesses and squared norm formulation.
Theorem 2 equality classification and higher tensorization corollaries
are NOT yet kernel formalized.

The mathematical proof comes from
https://github.com/mxym/math/tree/main/notes/complex-permanent-determinant .
AI-assisted authorship, lack of external peer review, and lack
of historical mathematical priority certification remain disclosed.

## Verified Mathlib-native matrix theorem

The additional kernel theorem
`ComplexPencilFull.matrix_squared_norm_iff` quantifies directly over
`A : Matrix (Fin 3) (Fin 3) ℂ`, uses **Mathlib**
`A.permanent` and `A.det`, and defines squared row norms as
`∑ j : Fin 3, Complex.normSq (A i j)`.

It proves the same *if-and-only-if five-term optimum* over all matrices.
The bridge module `MatrixBridge.lean` proves that the six-term
polynomial expressions are exactly Mathlib's matrix permanent
and determinant, by a complete six-permutation
enumeration and `Matrix.det_fin_three`.
`MatrixTheorem.lean` checks the passage from arbitrary
nine complex entries to the standard matrix object.

To replay the stronger endpoint after the seven earlier modules:

    lake env lean -o .lake/build/lib/lean/MatrixBridge.olean MatrixBridge.lean
    lake env lean MatrixTheorem.lean

The actual `MatrixTheorem.log` axiom check shows only
`propext`, `Classical.choice`, and `Quot.sound`.

## Sharp complex absolute-value estimate, kernel verified

The new `NormCanonical.lean` identifies the **literal usual complex
norm** version of the five-branch exact formula, including its
(2/\sqrt3) and (1/\sqrt3) constants. It supplies
`matrix_canonical_squared_iff`.

The new `AbsolutePencil.lean` proves the original paper's
**Theorem 1 absolute-value strengthening** by choosing an aligned
complex coefficient on the centered sharp disk and using the
already-verified coefficient lens. The theorem
`sharp_absolute_value` quantifies over all nine complex entries,
and proves

[
 |\operatorname{per}A|
 +(2/\sqrt3-1)|\det A|
 \le(2/\sqrt3)\prod_{i=1}^{3}\|A_{i,*}\|_2.
]

Separate Lean theorems `determinant_weight_sharp` (identity
permutation witness) and `prefactor_sharp` (all-ones matrix witness)
formally establish **joint coefficient optimality**.
Actual compiler `AbsolutePencil.log` verifies all three endpoints
with only Lean foundational axioms. No `sorry`.

**Still unformalized:** complete equality characterization and
complex-valued permutation tensorization, plus the paper's
probability-law interpretation.
