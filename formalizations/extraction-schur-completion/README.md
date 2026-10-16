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


Further actual finite-dimensional results:

- The literal Haar twirl is exactly an internally constructed finite
  Hilbert--Schmidt projection onto the actual permutation algebra. Its trace
  pairing, idempotence and uniqueness are proved for all dimensions.
- Copy-permutation traces and Gram entries equal dimension to the number of
  actual permutation cycles, derived by a fixed-word/cycle-coloring equivalence.
  The flat Haar average's moments, finite Gram equations, existence of a
  solution, uniqueness of the represented matrix, and exact purity formula are
  proved without assuming a nonsingular Gram matrix.
- The intrinsic support projector is central in both actual commuting algebras.
  Antisymmetrizing any more than `s` selected positions annihilates the actual
  rank-budget support, including in the presence of additional tensor factors.

These are new ordinary-compiled results. They do not enlarge the frozen audit
scope and do not close the intermediate-rank sharp asymptotic listed above.

The first actual classified blocks are now connected:

- The complete symmetric block has rank `choose(D+k-1,k)` and the literal Haar
  scalar `s^(-k) choose(s+k-1,k)/choose(D+k-1,k)`.
- The actual alternating block has rank `choose(D,k)`, internally obtained via
  explicit tensor/exterior maps, and Haar scalar
  `s^(-k) choose(s,k)/choose(D,k)` for `k ≤ D`.
- The actual rank-one Haar average equals `symmetricState`.
- For `k=s+1`, the support projector is exactly `I-P_alt` and its rank is
  `D^(s+1)-choose(D,s+1)`. For `k≤s`, the support projector is the identity.

The general-shape classification and the intermediate-rank sharp two-moment
asymptotic remain open in this continuation.

There is now an exact general-rank matrix ratio, independent of classified
Schur theory. With `Z(D,t,k)=sum_sigma t^(cycles sigma) P_(sigma inverse)`,
Lean proves internally:

- `Z(D,t,k)` is positive semidefinite, central, and all these matrices commute.
  It is `k!` times an explicit partial trace of the actual symmetric projector.
- `Z(D,D,k)` is positive definite and has nonzero determinant for every `D,k`.
- The genuine Haar average equals `s^(-k) Z(D,s,k) Z(D,D,k)^(-1)`.
- `rank Z(D,s,k)` is the actual support rank for `0<s≤D`, and the actual purity
  has the exact squared-ratio trace formula.
- Genuine joint eigenspaces span the original tensor space; the Haar eigenvalue
  there is `s^(-k) chi(s)/chi(D)`, with nonzero denominator proved internally.

Young-tableau identification and spectral concentration remain necessary for
both sharp intermediate-rank asymptotic moments.

The actual cycle operators now have a proved Jucys--Murphy insertion recursion
and finite product factorization. The genuine tensor-space Jucys--Murphy
matrices are Hermitian and commute pairwise, and their joint eigenspaces span.
The actual Haar eigenvalue on each nonzero joint vector is
`s^(-k) product_j(s+c_j)/product_j(D+c_j)`, with nonzero ambient denominator
proved internally. The joint values `c_j` have not yet been classified as
integer tableau contents or assigned their tableau multiplicities.

This continuation is paused at the user's request. All new results are
`BUILD_ONLY`: ordinary Lean compilation and selected standard-axiom checks,
with a separate new-scope empty-kernel audit still pending.
