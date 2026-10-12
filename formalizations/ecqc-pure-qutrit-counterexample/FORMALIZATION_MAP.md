# Pure qutrit ECQC: paper-to-Lean map

Baseline inspected: `mxym/math` main `2d67375906d729862d4eb085186a5fd5670ef390`. The current README, SOLVED_PROBLEMS, RESEARCH, formalizations, manuscript, and open Gaussian PRs were checked before this direction was selected. No tracked AGENTS.md exists at that baseline. Previously frozen releases are not modified.

## Closed proof chain

| Paper object / argument | Required mathematical proof | Lean endpoint(s) | Status |
|---|---|---|---|
| Quantum-state and entropy definitions | Actual complex density operators, partial traces, spectral von Neumann entropy | `QuantumCore`; `QuantumInfo` | Fresh compile + empty-kernel replay passed |
| Eq. (sigma3) and Section 2.2 reduced state | Normalized pure vector; PSD trace-one outer product; actual partial traces; quadratic operator identities | `psi_normalized`, `rho_density`, `partialTraceRight_rho`, `partialTraceLeft_rho`, `rho_idempotent`, `reduced_scaled_projection` | Passed |
| Spectral entropy deduction | Actual eigenvalues satisfy the operator polynomial; use trace-eigenvalue identity | `eigenvalue_zero_or_scale`, `entropy_scaled_projection`, `rho_spectral_entropy`, `reduced_spectral_entropy`, `reduced_density` | Passed |
| Four complete MUBs | Actual columns are orthonormal and every squared cross-overlap is 1/3 | `basis_orthonormal`, `basis_mutually_unbiased`, `completeMUB` | Passed |
| Born rule and literal rational table | General pure-density expectation identity; every actual joint outcome probability | `born_pureState`, `bornTable_eq`, `actual_born_probabilities` | Passed |
| Quantum and measured mutual information | Actual partial-trace spectral entropies; actual marginal and joint Shannon entropies | `rho_quantum_mutual_information`, `measured_mutual_information` | Passed |
| Original three-of-four minimum | All retained subsets, the full value set, and attainment | `retained_sum`, `retainedValues_singleton`, `ecqc_score_eq`, `ecqc_minimum_attained` | Passed |
| Explicit pure qutrit counterexample | Q=2 log 2, ECQC=3 log 2, strict violation with all physical validity proofs | `pure_qutrit_counterexample`, `exists_pure_qutrit_counterexample` | Passed |
| Universal prime-dimensional pure-state assertion | Negate its original universal quantifiers using the actual prime-three witness | `pure_prime_dimensional_ecqc_is_false` | Passed |

The endpoint names in the qutrit rows are in `ECQC.Qutrit`; the generic spectral/Born/definition endpoints are in `ECQC`. `PROOF_SOURCES.json` contains the complete list of 73 audited roots, including definitions as well as theorems. The eight mathematical modules are individually rebuilt from current source in a new directory. The resulting 35,401-declaration transitive closure is replayed into an empty kernel at trust level zero. The replay has no unproved quantum or analytic inputs beyond Mathlib's kernel-checked proofs and the standard logical axioms propext, Classical.choice, and Quot.sound.

## Deliberately unclaimed coverage

This closes the complete qutrit counterexample in the paper, and therefore its existential pure-state disproof. It does **not** formalize the whole prime-dimensional classification. In particular, the universal Holevo bound, the two-dimensional positive theorem, optimality of the 3/2 ratio, the five-dimensional constructions, all-prime analytic estimates, and full-Schmidt-rank witnesses are neither inputs to this certificate nor certified conclusions of it.

The manuscript's qutrit witness is already an explicit existing result. This contribution is its complete Lean proof, not a claim to have newly discovered the witness, first refuted unrestricted ECQC, or obtained external human peer review. The independent replay uses the same fixed Lean implementation in a separate empty kernel; it is not an independent implementation of Lean itself.
