# Intrinsic finite-rank tensor support

This is a separate Lean 4.34.1 / pinned Mathlib package. It does not change or
extend the parent package's frozen 86-root pure-state audit.

The matrix `rankBudgetProjector D k s` is constructed on the actual coordinates
`(Fin k → Fin D) → ℂ`. Its range is the span of actual product vectors whose
one-copy factors jointly span at most `s` dimensions. The finite basis and Gram
inverse construct its Hermitian idempotent; the caller supplies neither the
projector nor a rank/support certificate.

Compiled results include:

- Every actual rank-at-most-`s` matrix tensor power has left support in this
  projector. For Hermitian inputs the support is two-sided. Actual PSD and
  trace-one tensor semantics use `ExtractionSpectrum.tensorMatrix`.
- For positive blocklength, this space equals the span of ranges of all actual
  normalized PSD rank-at-most-`s` iid densities. The proof internally constructs
  normalized projections of the one-copy factor spans.
- The projector commutes with every actual identical one-copy linear action,
  including every `U^⊗k`.
- Perfect expectation for an effect with `1-M` PSD on the entire normalized
  rank-bounded iid promise forces `M * rankBudgetProjector = rankBudgetProjector`.
  The PSD zero-trace-pairing-to-zero-product lemma is proved internally.
- At `s=1` the projector equals the parent's explicitly counted symmetric
  projector. Its rank is the actual binomial coefficient. At `s ≥ D` it equals
  identity. Rank monotonicity, positivity for `D,s>0`, and the ambient `D^k`
  dimension bound are proved.
- Actual rectangular factorization and symmetric monomial contraction prove
  `rank P_s ≤ s^k * choose(D*s+k-1,k)` for all natural parameters. A fixed
  coordinate isometry proves `s^k ≤ rank P_s` when `s≤D`. Consequently, for
  `0<s≤D`, `log(rank P_s)/k → log s`.
- The actual rank divided by `b^k` tends to zero when `s<b`. The actual
  `sqrt(rank P_s)/b^k` tends to zero, and its positive reciprocal tends to
  infinity, when `b>0` and `s<b^2`. These give direct packing interfaces.
- The actual support is exactly the range of the fully explicit finite matrix
  `supportCoefficientMatrix D k s`, whose entries are occupation-projector
  entries. Consequently its matrix rank exactly equals `rank P_s`; this is a
  finite polynomial-coordinate identity without a Schur dimension premise.
- If `k≤s`, the projector is already identity, independently of `s≤D`.
  An explicit symmetric-rank bound is
  `rank(P_sym(E,k)) ≤ E^(E-1)*(k+1)^(E-1)` for `E>0`, with the corresponding
  logarithmic bound. The parent audit sources remain fixed.
- For any fixed actual matrix `X`, the span of the ranges of all actual
  `(U X U†)^⊗k` equals this same rank-budget space at `s=rank(X)`.
  The proof constructs source/target isometries and one actual unitary
  extension internally. A fixed actual density therefore has the same
  perfect-expectation support implication even with a nonflat nonzero spectrum.
  This supplies an exact-performance bridge, not a fixed-error profile.
- `flatCoordinateDensity D s hsD` is an explicit normalized coordinate
  projection. For `0<s≤D` its PSD, trace one, and exact matrix rank `s` are
  proved. Its actual tensor power has purity `s^(-k)` for every blocklength,
  including zero. No eigenvalue, density, rank, or moment certificate is an
  input to the resulting `exists_flat_rank_density` theorem.

This is **not yet a formal Schur-Weyl decomposition, the general numerical
Weyl/hook dimension formula, the sharp general-rank polynomial asymptotic, or a Haar
first/second moment identity**. The rank for intermediate `1<s<D` remains the
rank of the constructed actual projector, equivalently the finrank of the
intrinsic space, with the explicit bounds and exponential rate above. No
structure field assumes any of those missing conclusions.
Blocklength zero is supported by the construction and support theorems; the
minimality and perfect-promise implication explicitly require `0<k`.

Run `lake build`, then `python3 reproduce.py --check-only` or
`python3 reproduce.py --fresh`. The latter removes only this child's own build
output, replays the declared roots in an empty kernel at trust zero, rejects
same-type forged proofs, binds all local imported mathematical sources and
package configurations, and saves the bound source snapshot. It does not clear
or re-audit the old packages' output or historical roots. Their imported
declarations enter only as dependencies of this new audit.

Every saved reproduction records its literal root list and bound source
snapshot. A historical `LATEST.json` result validates that snapshot; compare
its source-manifest hash with the current `SOURCE_HASHES.json` before treating
it as evidence for newer sources. A separate `build-only-*` record explicitly
marks ordinary Lean-checked successors awaiting a source-frozen kernel replay.

Local dependencies are the parent symmetric-support package, the independent
matrix-projector factory, and the information-spectrum package (whose tensor
module depends on the spectral extraction core and original density package).
There is no dependency on the physical-protocol or minimax packages.
