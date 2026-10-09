# Sparse arithmetic: independently replayed proof foundation

**Verified foundation only. This is not a complete APPT maximal-purity release.**

The proof-preserving sparse polynomial implementation from parallel commit
`6b18f1f` is retained without changes. It represents a monomial by its list of
variable indices and proves evaluation laws for sorted insertion, monomial
multiplication, coefficient merging, integer scaling, polynomial multiplication,
and removal of zero coefficients. These laws hold without assuming that the
input polynomials are sorted; even the zero-fuel merge fallback preserves
real evaluation.

## Exact verification evidence

CI run **37948196219**, source commit
`b00c7a4360b3504cf63ffc63442f4564b779b08c`, passed the pinned Lean 4.34.1 / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` build and audit. Literal logs, the
workflow response, source hashes, root and closure lists are retained under
`verification/sparse-arithmetic-ci-20261009/`.

The seven exported roots replayed **5,166 declarations** in an initially empty
Lean kernel at **trust level zero**, with only `propext`, `Classical.choice`,
and `Quot.sound` allowed. The audit compares each replayed root type and its
universe parameters with the original declaration.

Two separate negative controls are required. First, the audit substitutes
`True.intro` for the proof of `eval_mul` and replays the modified closure in a
second fresh trust-zero kernel. The kernel rejects the theorem for a declaration
type mismatch. `True.intro` is explicitly included in the dependency closure,
so an unavailable declaration cannot explain this rejection. Second, a cubic
coefficient is changed from 3 to 2; `decide +kernel` proves the resulting
identity false, and Lean exits with code 1. The neighboring correct cubic
identity is itself one of the successfully replayed roots.

The first audit attempt also obtained the expected proof and coefficient
rejections, but its shell matcher expected an older tactic diagnostic. Run
37948196219 fixes the matcher to require the actual pinned-version diagnostic
that the proposition is false; no proof, assumption, or kernel check is weakened.

## Reproduce

From this package directory after obtaining the pinned Mathlib cache:

```sh
lake build +APPT.SparsePolynomial
mkdir -p .lake/build/lib/lean/Verification
lake env lean -j1 -M12288 -o .lake/build/lib/lean/Verification/ReplaySupport.olean Verification/ReplaySupport.lean
lake env lean -j1 -M12288 SparseArithmeticAudit.lean
lake env lean -j1 -M12288 RejectSparseCoefficient.lean
```

All commands except the last must succeed. The last command must fail specifically
because the altered identity is false. The workflow
`.github/workflows/appt-sparse-arithmetic.yml` checks both exit codes and the
corresponding diagnostics, and retains all evidence. `Verification/ReplaySupport.lean`
is audit code, not an assumption or dependency of the mathematical theorems.

## Remaining scope

This foundation is intended to replace long finite-certificate expansions by
small kernel-checkable computations. The bounded finite certificate modules,
final all-dimension state theorem, complete Lake build, and full theorem-closure
audit must still pass together before the entire APPT problem can be declared
formally complete. The immutable interim release is not modified.
