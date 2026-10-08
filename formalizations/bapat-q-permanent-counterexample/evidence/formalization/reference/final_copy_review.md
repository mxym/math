# Final public-copy verification

Date: 2026-10-08 UTC.

## Result

**PASS.** The reviewed public package faithfully contains the verified counterexample to the original q-permanent monotonicity conjecture for non-diagonal complex Hermitian positive definite matrices on [-1,1]. The public copy preserves the exact data, polynomial definitions, normalization, explicit positive-definite perturbation, and rational interior-q witness.

This is model-conducted mathematical and exact-arithmetic review. It is not external journal peer review, proof-assistant certification, or a determination of historical priority. The real-symmetric restriction is not settled by this package.

## Frozen mathematical inputs

The 200-row CSV was compared byte for byte with the independently reviewed input, including its order and line endings. Its SHA256 is

`9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`.

The finite proof has SHA256

`7c5b37b1326ea5431e2b3ec08dc3cd677899265dedd7fbd6d353d03e58b0b4ef`.

The existence proof has SHA256

`9d6a3d7e1e150c44cbf11f2b1573392af512cbbc59e595fe03afe80ad4a80a70`.

The last proof differs from the preceding reviewed public copy only by replacing “since F(u)>0” with “since |F(u)|>0” in the concentration explanation. This makes the notation correct for a complex-valued polynomial and changes neither the argument nor any formula or constant.

The three verification programs retain their reviewed bytes:

- `verify_recurrence.py`: `61630fe46bdde35e083517f13f7737f7264ad160224a296ba0977874fe058b65`
- `verify_pairs.py`: `275fb7e3e7bc42cf0d86e0be85459287def10c7f8712ef222a31930c5b7a3a74`
- `verify_by_pair_deletion.py`: `4f8854751bbe1de5052741900e06ecb821a2630b0385c931e7ee390282e8ab41`

## Mathematical-scope checks

The public finite proof and its independent referee report retain:

1. The inversion-weighted definition P_q(A), with fixed CSV order.
2. A_ij=a_i conjugate(a_j)+b_i conjugate(b_j), F=product_i(a_i x+b_i y), and S=sum_(i<j)(a_i b_j-b_i a_j) product of the remaining factors.
3. The degree-d norm sum_k (d-k)! k! |coefficient_k|^2, and the independently derived identity 2P'_1(A)=binom(n,2)||F||^2-||S||^2.
4. n=200, N=19900, epsilon=[4N n! n 1601^(n-1)]^(-1), and B=A+epsilon I, which is non-diagonal and positive definite.
5. q0=1-[8N(N-1)n!1601^n]^(-1), with 0<q0<1 and P_q0(B)>P_1(B).
6. The distinction between the original Hermitian conjecture and statements extending past q=1 or concerning other permanent functions.

The public existence proof retains the correct unitary determinant phase, uniquely peaking extra factor, truncated real-Cauchy pair-score estimate, contiguous replication, factorial normalization, and fixed-base-before-replication quantifier order. It describes pi^2/8 as a lower asymptotic benchmark, not an unproved universal exact limit.

## Actual clean-copy executions

All three programs were executed with ordinary Python, without `-O`, in an isolated copy of the frozen public folder:

```sh
python verify_recurrence.py
python verify_pairs.py
python verify_by_pair_deletion.py
```

All exited successfully. The source folder remained unchanged throughout execution.

The recurrence and both direct pair-deletion implementations independently recomputed the same permanent P, second norm Q, scaled permanent NP, and positive difference D=Q-NP. All four exact integers agree with `expected_values.json`. D is even, has 816 decimal digits, and satisfies

23NP < 1000D < 24NP.

The regenerated independent coefficient certificate agrees with `independent_certificate.json`. Its 20 small-order Gram-matrix full-permutation tests and five general-complex-matrix identity tests all passed. The exact epsilon and q-gap denominators agree between the independently generated certificates.

The pair-deletion run's elapsed-time field naturally varies; comparison of reference and fresh results used the exact mathematical fields. No timing value or floating-point approximation is used to prove an inequality.

## Public-copy hygiene and completeness

The package manifest's file sizes, SHA256 hashes, and Git blob identifiers were recomputed directly. The SHA256 summary was checked against every listed file. The integrity files exclude the appropriate self-referential entries, rather than claiming circular self-hashes.

The reviewed payload has no unlisted files or symlinks. The final addition of this report requires only regenerating the integrity files and checking that all previously approved payload hashes remain unchanged.

All mathematical inputs and verifier dependencies use files in the public package. The original auditor's program and full coefficient certificate are included, so the 25 small-order tests cited in `referee_report.md` remain reproducible. The two complete mathematical review reports are included; references to private working-directory paths were replaced by public relative filenames without changing their mathematical assessments.

The public files were checked for internal routing identifiers, private workspace paths, research-message transcripts, and unrelated content. None is included. The scholarly material consists of the proofs, original reviews, data, code, exact outputs, and source references; no third-party paper is reproduced in full.

The proposed repository README addition accurately identifies the complex-Hermitian scope, the order-200 witness, the two proofs, three verifiers, and the stated verification and novelty limits. It preserves earlier work on the beyond-q=1 extension as a separate historical result.

## Publication boundary

This review approves the exact mathematical payload identified above. It does not authorize changing the data, row order, constants, proof formulas, or verification programs. Any such change needs renewed mathematical review. An additive copy of this report and regenerated integrity metadata can be checked without rerunning unchanged mathematical computations.
