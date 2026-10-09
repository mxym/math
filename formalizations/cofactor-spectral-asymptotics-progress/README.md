# Permanental cofactor spectra: upper bounds and actual finite ring construction

This package completely proves the actual first-compound indicator inequality and the
spectral/logarithmic upper half of the sharp asymptotic theorem. **The matching lower bounds
and the four sharp limit equalities are not yet Lean formalized.** This is a progress checkpoint
for coordination, not a claim that Theorem 1 is fully formalized.

The reference is [the fixed mathematical source](https://github.com/mxym/math/tree/df6d94763c852c3cf69f29c5fa95c51f88378160/notes/sharp-cofactor-spectral-asymptotics).
For complex Hermitian PSD A, the actual matrix is
`C(A)[i,j] = A[i,j] * permanent(A with row i and column j deleted)`.
The minor is not transposed. Real directions allow complex Hermitian matrices.

## Completed theorems

- `compound_psd`: the actual compound is PSD in every rank, including singular inputs.
- `compound_indicator_sum`: every subset S satisfies `1_S* C(A) 1_S <= |S| permanent(A)`.
- `compound_largest_eigenvalue_upper`: for positive permanent,
  `lambda_max(C(A))/permanent(A) <= 4+H_(N-1)`.
- `realCompound_largest_eigenvalue_upper`: for the entrywise real part,
  `lambda_max(Re C(A))/permanent(A) <= 2+H_(N-1)/2`.
- Six `*_eventual_log_upper` theorems: for every epsilon>0, all sufficiently large N
  satisfy the normalized upper bounds `1+epsilon` or `1/2+epsilon` for unrestricted PSD,
  exact-rank-two correlation, and positive-definite correlation classes.

The full route is actual permanent/cofactor identities, complex polynomial Fock Gram
factorization, finite weighted symmetrization, explicit contraction squares, indicator
positivity, Abel summation and exact sorting, signed and complex vector decomposition,
harmonic estimates, standard Hermitian eigenvectors, and conditional suprema with the
empty-set cases handled explicitly. See [the semantic review](SEMANTIC_REVIEW.md).

## Verification of these exact bytes

All **54** owned modules were fresh compiled into a new isolated output directory. All
**553** owned declarations, including compiler-generated declarations, were
audited; their complete **55068**-declaration transitive closure was
replayed from an **empty kernel at trust level 0**. Requested endpoints had a union closure
of 54915 declarations. The checker confirms only the three
standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with their signatures
checked. There are no custom axioms, `sorryAx`, unsafe or partial owned declarations, or audit
exclusions. An intentionally invalid proof was rejected by the empty trust-zero kernel.
The official shared cache fingerprint was unchanged throughout the verifier run.

`verification/` contains the exact declaration inventory and closures (compressed), endpoint
types, all compilation logs, replay results, axiom signature checks, negative control, and cache
check. This certificate covers the frozen 54-module source set only. Later lower-bound work
requires its own fresh certificate. The source-to-statement review is by the implementing
agent; no external human review is claimed.

Pinned Lean: **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Pinned mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Reproduce

Ordinary compilation uses the pinned Lake project: `lake build`.
For independent fresh compilation, all-owned dependency audit and empty-kernel replay, use
already installed official dependencies with the supplied verifier:

```sh
python3 reproduce.py --output /new/verification-output \
  --toolchain /path/to/lean-4.34.1 \
  --packages-root /path/to/pinned-packages \
  --cache-root /path/to/existing-cache
```

The output path must not already exist. The reproduction script installs nothing, downloads
nothing, and does not use any prebuilt owned module. `SHA256SUMS` covers all packaged files.

## Verified lower-bound lemmas

- `geometric_separation_product_bound`: the complete exact entropy/product estimate with
  E(b)=b^(b/(b-1))/(b-1), derived using a finite Gibbs inequality and shifted-sum mean bound.
- `groupedSignCombination_square_average`: exact weighted finite sign averaging, including
  collisions of degree sums, and `groupedSignCombination_has_small_choice`: an actual finite choice.
- `marked_coefficient_quadratic_lower`: keeping one actual Fock coefficient bounds the actual
  compound quadratic form from below in every rank.

## Actual finite ring construction

- `exists_signed_root_ring`: actual complex roots with prescribed positive squared radius,
  either coefficient sign, exact homogeneous product, zero root sum and squared root sum,
  and the exact imaginary second moment. Root existence is proved using official algebraic closure.
- `normalizedBinaryGram_rankTwoCorrelationAdmissible`: unit-diagonal PSD Gram matrices,
  strictly positive permanent, and exact rank two from a zero and a nonzero slope.
- `normalizedBinaryGram_permanent_ratio`: the actual permanent equals
  `N! * gamma^2 * sum_j normSq(coeff_j)/choose(N,j)`.
- `signedRingPolynomial_has_small_choice`: an actual sign assignment bounds this coefficient
  ratio by the diagonal subset sum, even when different subsets have equal degree.
- `exists_rankTwoCorrelation_ring_bound`: combines actual root rings and zero reserve,
  transports them to the standard `Fin N` matrix index, proves all moments and exact rank-two
  correlation admissibility, and bounds the permanent by the explicit binomial-weighted subset sum.
- `normalizedBinaryGram_complex_test_lower` and `normalizedBinaryGram_real_test_lower`:
  the actual marked coefficients prove the complex-slope and real-imaginary test-vector
  Rayleigh lower estimates under an explicit permanent denominator estimate. This denominator
  interface is not counted as a proved analytic small-tail bound.

## Remaining work

The explicit subset sum still needs the factorial/binomial and geometric tail estimates
that make it at most `1+eta`. The geometric dimension recurrence, every-large-dimension
lower bounds, sharp parameter limits and positive-definite lower perturbation remain unfinished.
The main sharp logarithmic limit theorem is not yet complete. Later development bytes require
their own fresh compilation, all-owned audit and empty-kernel replay.
