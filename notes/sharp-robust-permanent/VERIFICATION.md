# Verification and trust boundaries — permutation permanent stability

Date: 2026-10-08. Primary mathematics: [paper.md](paper.md). Research guide: [README.md](README.md).

## Fresh public-source replay

An authorized Windows desktop, Python 3.12, and SymPy 1.14 were used. All six scripts were freshly retrieved individually from the public mxym/math main branch into D:\mcp-workspace\math-research\permanent-validation-20261008 before execution; the runner stopped on any nonzero exit status.

**Result: SIX CHECKERS PASSED FROM PUBLIC MAIN.** No floating-point output is used as proof input.

| Checker in code/ | What is checked exactly | Boundary |
| --- | --- | --- |
| check_examples.py | Integer exponent comparisons, subset identities, rational cyclic mixtures | Illustrative; not the all-n theorem |
| check_atom_modulus.py | Rational S_n extremizers and uniform marginals for n=3,4,5,6 | The all-n proof is analytic |
| check_s3_exact.py | Gram identity, principal minors, determinant factorization in Q(sqrt3), S3 parity | The PSD inference still uses written AM-GM |
| check_s3_phase.py | Rational p=5/2 counterexample, K3,3 incidence, equality kernels | Does not prove every-exponent radius |
| check_local_gaps.py | Integer/root inequalities and rational lower margins V/100, S/1200 | Arbitrary-real-exponent Taylor and compactness arguments remain analytic |
| check_doubly_transitive.py | Nine finite symmetric, alternating, affine group witnesses and exact TV/marginal identities | The all-group theorem is analytic |

To reproduce, run the six Python files above from the directory notes/sharp-robust-permanent/code. Only SymPy is additionally required for check_s3_exact.py and check_s3_phase.py.

## Proof-dependency map

- **Theorems 1–2:** import Bristiel–Caputo (2024), Corollary 1.14, for the uniform permanent inequality. Quantitative perturbation bounds, sharp-order asymptotics and nonidentical tensorization are argued in this note.
- **Theorems 4 and 6:** self-contained exact S3 L2 radius and all equality cases, using the displayed 3x3 positive semidefinite Gram matrix and AM-GM. Symbolic identities were replayed.
- **Theorem 7 and Corollary 8:** analytic two-row perturbation; the p=5/2 example is witnessed by two strict rational fifth-power comparisons.
- **Theorem 9 and Propositions 10–11:** finite Gibbs entropy duality and exact K3,3 incidence reduction. The two-level stationary condition applies only in the *interior*.
- **Theorem 12:** analytic uniform local gaps near four classified endpoint extremizers and a strict compact-complement argument. It proves a nonempty exact interval but does not yield an explicit numeric lower endpoint.
- **Propositions 13–14:** entropy Hessian calculation and explicit rational local deficits.
- **Theorem 15:** self-contained group-action proof via fixed-point counts, Burnside's lemma, double transitivity and disjoint-support measures. No use of Bristiel–Caputo.

## Outstanding items and claim limits

1. No external human peer review, independent second-model line-by-line audit, or Lean formalization of the complete expanded manuscript has been performed.
2. The exact formula for the three-row radius throughout q3 < p < 2 remains open; only an unspecified nonempty terminal interval near 2 has been proved.
3. The exact lower endpoint p0 in Theorem 12 is non-effective. An independently replayable compact-complement margin is the immediate target for an explicit rational p0.
4. The exact radius for 2 < p < 3 is not known: the singleton formula has been rigorously disproved there by a two-row perturbation.
5. Full literature novelty and mathematical priority checks remain pending; no first-discovery or external-verification claim is warranted.

These finite checkers support specific algebraic and finite combinatorial assertions. They are **not substitutes** for the arbitrary-parameter analytic proofs.
