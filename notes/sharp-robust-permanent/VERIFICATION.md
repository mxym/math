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


## Additional complete orbital certificates (October 8 continuation)

The existing six checkers above were all replayed directly from published main with zero exit status. Two further public checkers were subsequently freshly fetched and executed, both passing:

- code/check_edge_action_s5.py: enumerated all 120 vertex permutations, verified seven cycle-type rows for fixed and adjacent edge statistics, checked all 100 edge-to-edge marginals for two explicit primal probability distributions, the exact 1/3 dual range, exact 1/3 atom excess, and probability positivity. Output ended: S5 EDGE-ACTION PRIMAL-DUAL CERTIFICATE REPLAY PASSED.
- code/check_all_two_subset_actions.py: for each n=4,...,40, enumerated every integer partition (hence every conjugacy type), verified every even/odd dual inequality with Fraction arithmetic, checked exact moment matching and positivity of the primal class mixtures, and matched the closed formula C_n. The published checker was freshly downloaded from main **after its final target-assertion correction**. Output ended: PASS: all 37 degrees, full conjugacy partitions, exact dual extremes, primal moments, and rational positivity.

**Important distinction:** Theorem 17 is an all-parameter theorem proved by symbolic quadratic inequalities (77)--(86) and explicit class measures (73)--(75). Partition enumeration through n=40 is supplementary, not an extrapolation from finite cases. Theorem 16 has an independent finite all-120-element proof replay, with mathematical primal and dual inequalities also written in full.

**General reduction:** Theorem 18 is an exact finite-dimensional LP duality argument written out in the manuscript. It establishes a rational primal-dual certificate interface for arbitrary finite permutation actions, not a claim that every representation has a simple closed formula.

**Outstanding:** external mathematical peer review and systematic novelty research remain pending, together with the unresolved S3 exponent interval q3<p<p0, exact 2<p<3 radius, an effective p0 certificate, and higher-rank k-subset orbital optima for k>=3. The expanded paper is not Lean formalized.


## Independent fixed-certificate three-subset replay

A further **fixed-scope finite theorem** is established by Section 19: the exact sharp atom-vs-TV coefficients for S_n acting on three-element subsets in every degree 6≤n≤23 (complementation and previous theorems handle n=3,4,5).

**Frozen machine-readable input:** certificates/three_subset_n6_23.json contains 18 complete rational primal/dual entries, each with explicit conjugacy-class supports and weights, three dual coefficients, both dual extrema and the claimed exact optimal fraction. No float values are stored.

**Discovery/generation is separate:** code/generate_three_subset_certificates.py computes the fractions by exact Fraction-based Gaussian elimination on pinned class supports. It is neither imported nor executed by the checker.

**Independent verifier:** code/check_three_subset_certificates.py uses only Python standard-library integers and fractions; it loads the fixed JSON, independently enumerates all integer partitions of 6,...,23, calculates each representative's image intersections for all three-element subsets, checks every one of the four marginal-orbital moment equalities and *every* classwise dual inequality, verifies the exact upper-lower primal equality, class-size totals, disjoint supports, and positivity of a small rational attaining perturbation. Its finite loops have explicit terminating degree and partition bounds.

**Fresh public-source replay:** On the authorized Windows machine a new isolated folder was created under D:\mcp-workspace\math-research\three-subset-public-replay. Both the standalone checker and frozen JSON were freshly downloaded from public GitHub main (not copied from the prior local generator). The replay completed all 18 degrees without an error and printed:

    EIGHTEEN EXACT THREE-SUBSET CERTIFICATES REPLAYED; all classes, primal/dual bounds, rational positivity.
    FRESH PUBLIC JSON AND INDEPENDENT CHECKER VERIFIED

This is a complete **finite exact computer-assisted proof** under the usual trust in the published short checker, Python integer arithmetic, and the finite LP duality mathematical argument of Theorem 18; it is not a Lean kernel formalization or a solution to the full all-degree three-subset problem. Independent human review and a literature novelty audit are still pending. The fixed certificate covers only the stated degrees n=6,...,23; no extension to n≥24 is inferred.
