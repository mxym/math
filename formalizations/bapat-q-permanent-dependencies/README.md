# Actual Bapat q-permanent endpoint and perturbation dependencies

This package proves the actual universal deleted-minor endpoint identities
and the positive-definite perturbation and explicit-interval transfer chain.
The mathematical objects are the actual inversion-weighted polynomial,
actual permutations, actual complementary-row/column bijections, actual
matrix determinants and positive-definite Gram perturbations.

See [PROOF.md](PROOF.md) for the complete proof of this dependency chain.
It corresponds to Sections 2 and 5 of the archived
[complex order-200 counterexample](../../notes/bapat-q-permanent-counterexample/proof.md).
The same universal algebra can also be used in the separate
[real-symmetric existence proof](../../notes/bapat-real-symmetric-existence-counterexample/proof.md).

**This package does not certify either complete counterexample.**
For the finite counterexample, the actual Gram/Bargmann correspondence,
closed polynomial recurrence semantics, exact order-200 integer certificate
and its negative endpoint are separate required ingredients. The
[parallel complete formalization](../bapat-q-permanent-counterexample/README.md)
now supplies those ingredients for the existential original conjecture
counterexample. It does not choose the paper's specified rational parameters.
Joining its verified input to this package's explicit-parameter wrapper
requires an additional definition and input-correspondence proof.
For the real existence proof, the equidistribution, concentration and
rational approximation arguments also remain separate obligations.
No missing bridge is supplied here as a custom axiom or a premise asserting
the counterexample itself.

## Formal statements

- [EndpointDefect.lean](EndpointDefect.lean) proves the actual derivative
  identity for every complex matrix, including orders zero and one.
- [MinorPermanent.lean](MinorPermanent.lean) constructs the exact
  prescribed-permutation/complementary-bijection correspondence and
  identifies the result with `Matrix.permanent` under any relabeling.
- [HermitianReality.lean](HermitianReality.lean) proves that the actual
  q-permanent is real on the real axis for a Hermitian matrix.
- [EndpointBridge.lean](EndpointBridge.lean) proves the quantitative
  bounds for the actual endpoint derivative and the actual q-permanent.
- [PositiveDefiniteViolation.lean](PositiveDefiniteViolation.lean)
  constructs the explicit positive-definite perturbation and interval.
- [CounterexampleTransfer.lean](CounterexampleTransfer.lean) concludes
  failure of monotonicity on `[-1,1]` from an actual Gram input satisfying
  a quantified entry bound and `Re P′₁≤−1/2`, for order at least three.
  It proves a transfer theorem; it does not assert that such an input exists.

The finite-product bound covers empty products and zero radius. The real
polynomial derivative estimates handle exponents zero and one. The input
dimension bounds are proved, and negative derivative implies actual
non-diagonality, rather than leaving that hypothesis unchecked.

## Independent reproduction

Use official Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and the exact nine dependency
revisions in [lake-manifest.json](lake-manifest.json). With those packages
and their official build cache in a Lake dependency project, run:

```bash
python3 formalizations/bapat-q-permanent-dependencies/replay.py \
  --lean /path/to/leanprover--lean4---v4.34.1/bin/lean \
  --dependency-project /path/to/dependency-project \
  --output /path/to/new-output-directory
```

The output directory must not exist. The driver verifies package revisions,
freshly compiles the frozen mathematical source as one bundle without any
owned `.olean` input, audits every owned theorem's axioms, and replays the
entire dependency closure from an empty kernel at trust level zero. The
final theorem types and universe parameters must remain unchanged.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The proof
source contains no admissions, custom axioms or native-decision oracle.

Three positive controls include constant and linear polynomials and the
omitted-negative-endpoint example. The intentionally false reverse
interval for the increasing function `f(q)=q` must be rejected by Lean.
The replay collector is a metaprogram outside the mathematical proof closure.

The verified run checked **52 owned theorems** and replayed **21571 declarations** from an empty kernel. All three positive controls passed, and the false interval was rejected.

The exact source inventory is [MODULES.json](MODULES.json).
Recorded source hashes, axiom output, kernel replay and negative-control
evidence are in `verification/`. `check_record.py` checks the byte integrity
and bundle correspondence of that record; it does not perform a new Lean
replay. Mathematical scope is measured by the actual statements above,
not by the number of declarations replayed.
The [internal semantic review](reviews/perturbation.md) checks the actual
four endpoint files and states its scope; it is not external professional
peer review or a second kernel replay.

[ENDPOINT_SCOPE.md](ENDPOINT_SCOPE.md) and `endpoint-sha256.json` preserve
the earlier frozen six-module endpoint handoff. Its mention of the parent's
perturbation work describes that handoff stage; the completed perturbation
modules and their present scope are documented above.
