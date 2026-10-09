# Permanental cofactor spectra: complete upper-half formalization

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

All **30** owned modules were fresh compiled into a new isolated output directory. All
**386** owned declarations, including compiler-generated declarations, were
audited; their complete **48920**-declaration transitive closure was
replayed from an **empty kernel at trust level 0**. Requested endpoints had a union closure
of 48763 declarations. The checker confirms only the three
standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with their signatures
checked. There are no custom axioms, `sorryAx`, unsafe or partial owned declarations, or audit
exclusions. An intentionally invalid proof was rejected by the empty trust-zero kernel.
The official shared cache fingerprint was unchanged throughout the verifier run.

`verification/` contains the exact declaration inventory and closures (compressed), endpoint
types, all compilation logs, replay results, axiom signature checks, negative control, and cache
check. This certificate covers the frozen 30-module source set only. Later lower-bound work
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

## Remaining work

The finite geometric entropy estimate, signed root-ring construction, exact finite sign
averaging bound, every-large-dimension lower estimate, exact rank-two correlation construction,
sharp parameter limits, and positive-definite lower perturbation remain to be formalized.
No unproved lower input has been added to the theorem assumptions.
