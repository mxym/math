# Full Lean verification of the sharp complex permanent–determinant coefficient lens

**Status:** A complete Lean 4.34.1 / Mathlib proof of Theorem 1A from
the public complex three-row permanent–determinant manuscript.
Theorem 1B (the five-term exact norm formula for *every* coefficient)
and all equality classifications are not yet fully formalized.

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
    lake env lean Main.lean
    sha256sum -c SHA256SUMS

The original true compiler outputs are included:
cert-build.log, psd-build.log, Link.log, Main.log.
In Main.log the built-in Lean axiom reports for the two endpoints
and three core dependencies list only
propext, Classical.choice and Quot.sound.
No sorry, admit, native_decide, unsafe or custom axiom appears
in the owned proof files.

## Precise limitation

Complete for Theorem 1A (complex sharp lens equivalence) and its
optimal coefficient. NOT complete for the stronger Theorem 1B exact
five-term coefficient-dependent operator norm, or Theorem 2 equality
classification. These remaining targets require additional fully
checked optimality witnesses and parameter analysis.

The mathematical proof comes from
https://github.com/mxym/math/tree/main/notes/complex-permanent-determinant .
AI-assisted authorship, lack of external peer review, and lack
of historical mathematical priority certification remain disclosed.
