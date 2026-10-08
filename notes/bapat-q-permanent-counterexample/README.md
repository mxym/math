# A counterexample to Bapat's q-permanent monotonicity conjecture

This package gives a complete finite counterexample for the original interval −1 ≤ q ≤ 1 and an independent non-computational existence proof. The witness and its positive-definite perturbation are complex Hermitian matrices. This disproves the unrestricted Hermitian conjecture; it does not settle the restriction to real symmetric matrices.

This is a separate original-interval construction, distinct from a real order-four counterexample to a later proposed extension beyond q=1.

For the 200 rows listed in `counterexample_vectors_n200.csv`, form the complex Gram matrix A=VV*. Let n=200, N=n(n−1)/2, and

- ε = [4N n! n 1601^(n−1)]⁻¹;
- B = A + εI;
- q₀ = 1 − [8N(N−1)n!1601^n]⁻¹.

Then B is non-diagonal Hermitian positive definite, 0<q₀<1, and P_q₀(B)>P_1(B). Here P_q uses the inversion count of permutations, with the CSV row order fixed.

## Read the proofs

- `proof.md`: full finite construction, endpoint identity, exact integer certificate, positive-definite perturbation, and explicit rational q₀.
- `asymptotic_existence_proof.md`: separate CP1 equidistribution, ordering, and repetition argument. It gives the strict lower asymptotic benchmark π²/8>1.

The two arguments are logically independent after their common elementary endpoint identity.

## Reproduce the exact certificate

Python 3 and its standard library suffice. No third-party packages, numerical integration, optimization, or floating-point arithmetic are required.

```sh
python verify_recurrence.py
python verify_pairs.py
```

Both verify a strict rational margin between 23/1000 and 24/1000 in the endpoint criterion. They use independently implemented algorithms:

1. `verify_recurrence.py` builds the two binary forms by a polynomial recurrence.
2. `verify_pairs.py` builds the second binary form directly from all 19,900 pair-deleted products, using exact Gaussian-integer synthetic division with remainder checks.

The second verifier writes `verification_pairs_result.json`; a reference run is included. The expected exact permanent, second norm, scaled permanent, and positive margin are in `expected_values.json`. These stored values are compared with fresh calculations; they are not used to establish the sign.

The CSV uses columns `a_real,a_imag,b_real,b_imag`, without an index column. Its row order is part of the example. Its SHA256 is:

`9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`

All coordinates have absolute value at most 20. The maximum squared row norm is 432. The positive margin is an 816-digit integer, reproduced in `verification_recurrence_result.txt` and `expected_values.json`.

## Scope and verification status

The source formulation is Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14(4) (2020), pp.915–919, especially p.915. It concerns complex Hermitian positive definite matrices and the original interval [-1,1]. See the source and bounded literature-check discussion in `proof.md`.

The mathematical argument and exact arithmetic have passed independent model-conducted review using distinct implementations. This is not external journal peer review. This package does not assert proof-assistant certification or historical priority. It does not rely on a numerical optimization result as proof.

- `referee_report.md`: full finite-counterexample audit, source-scope checks, and exact-arithmetic trust boundary.
- `asymptotic_audit.md`: full independent review of the separate non-computational existence proof.
- `verify_by_pair_deletion.py`: the original independent auditor's verifier, including 20 small-order full-permutation tests and five general-complex-matrix identity tests. Run `python verify_by_pair_deletion.py` from this directory. Its complete generated coefficient certificate and reference console output are `independent_certificate.json` and `verification_pair_deletion.txt`.

Use ordinary Python without `-O`: the verifiers use assertions for their checks. The two pair-deletion implementations are separate programs; the primary algorithmic cross-check is between the recurrence and direct pair deletion. Timing fields in freshly regenerated results may differ from the reference runs.

`MANIFEST.json` lists the immutable payload's file sizes, SHA256 hashes and Git blob identifiers. `SHA256SUMS.json` additionally covers that manifest; neither file claims a circular self-hash. The CSV bytes and row order must be preserved. Complete repository author information and AI-assistance disclosure appear in [AUTHOR.md](../../AUTHOR.md).
