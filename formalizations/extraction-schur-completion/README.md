# Schur and Haar completion: independent continuation

This package extends the frozen 608-root extraction phase in a new scope. It
does not modify or enlarge that phase or the historical audit scopes.

Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` are fixed.
Run `lake build` after configuring the repository's shared dependency cache.
Ordinary compilation is currently verified; a new empty-kernel audit is pending.

The actual matrix results proved here include:

- Compactness of the original one-copy unitary matrix group and its normalized
  Haar probability, without a compactness or measure witness from the caller.
- The literal matrix-valued Haar orbit average, its integrability and density
  properties, and its exact range and rank. For any fixed density, its range is
  the intrinsic minimal rank-budget support at every blocklength, including zero.
- Equivalence between exact expectation on the Haar average and exact expectation
  on every point of the actual one-copy unitary orbit, under a positive deficit.
- Tensor-unitary invariance, the exact scalar purity integral
  `Tr(Ω²) = ∫ Tr(X U X U†)^k dU`, and `rank(P) Tr(Ω²) ≥ 1`.
- Actual tensor-position permutation matrices and the centralizer identity:
  a matrix commutes with every copy permutation precisely when it belongs to the
  complex span of genuine one-copy matrix tensor powers. This centralizer has
  dimension `choose(D²+k−1,k)`. The proof uses actual occupation fibers and
  polynomial evaluation, rather than an assumed Schur decomposition.
- The reverse centralizer identity: commuting with every genuine tensor unitary
  is equivalent to membership in the span of genuine copy-permutation matrices.
  Its finite-dimensional bicommutant proof, singular polar factorization, and
  finite Fourier phase interpolation are internal. Thus the unclassified mutual
  centralizer form of Schur–Weyl is now proved on the original coordinates.
- Explicit cross-Weyl products, their lower bound one, and the polynomial exponent
  and leading constant along every sequence of normalized row lengths converging
  to the uniform vector. The reciprocal pointwise limit is also proved.

The classified Young-diagram Schur decomposition, identification of its dimensions
with the Weyl and hook products, the actual Schur–Weyl probability law, its
exponential concentration, and the general-rank two-moment asymptotic are still
missing. In particular, this package does **not** yet prove
`r_(k,s) ~ c_(D,s) s^k k^(s(D-s))` or `r_(k,s) Tr(Ω_(k,s)^2) → 1` for intermediate
rank. A pointwise Weyl-product limit does not supply either expectation limit.

See [PROOF_ROUTE.md](PROOF_ROUTE.md) for the ordinary proof check, primary sources,
and exact interfaces that remain to be connected.
