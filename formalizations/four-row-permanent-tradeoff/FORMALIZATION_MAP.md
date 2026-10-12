# Paper-to-Lean correspondence

Initial selection baseline: `b8a6ab4` on `origin/main`. Implementation worktree
was subsequently based on `21e1f76`. README.md, SOLVED_PROBLEMS.md, RESEARCH.md,
formalizations and the relevant paper were inspected. No AGENTS.md existed
in the initial tree. Gaussian all-k work still exposed an unproved sharp
perimeter premise, with parallel developments in PRs 3–6 and 8–9. The present
four-row theorem had a complete written proof and exact Python identities,
but no Lean proof of the actual analytic matrix result.

Source: `notes/four-row-permanent-tradeoff/PAPER.md`.

| Paper statement | Necessary mathematical proof | Checked Lean statement | Coverage |
| --- | --- | --- | --- |
| Eq. (4), n=4 | Complex norm-square expansion | `symEnergy_identity`, `altEnergy_identity` | Complete |
| Theorem 3, n=4 specialization | Both Cauchy bounds for the actual overlap | `pair_bound` | Complete, arbitrary actual complex rows |
| Eq. (8) | Balanced Laplace expansion of actual permanent/determinant | `permanent_laplace`, `det_laplace` | Complete; all 24 permutations checked by the kernel |
| Eq. (9)–(10) | Complex Cauchy and weighted two-dimensional Cauchy | `permanent_sq_bound`, `det_sq_bound`, `weighted_laplace_bound` | Complete |
| Theorem 1 inequality | Row-energy bounds, including zero rows | `sharp_four_row` | Complete for every A and c >= 0 |
| Theorem 1 optimality | Flat and identity witnesses | `matrix_bound_iff`, `matrix_attainment`, `exact_tradeoff_norm` | Complete |
| Corollary 2 | Triangle bound and even/odd witnesses | `pencil_bound_iff`, `exact_real_pencil_norm` | Complete for every real t |
| Theorem 1 all equality cases; Theorem 4 | Pairwise deficit, support and phase rigidity | Not included in v1 | Written proof only |
| Theorem 3, arbitrary n | General finite-sum energy identities and sharpness | Not included in v1 | Written proof only |
| Convex objectives and tensorization | Additional analytic/functional arguments | Not included in v1 | Written proof only |

The six proof sources and all 67 named owned definitions/theorems were
rebuilt and replayed in the v1 evidence. No mathematical assumption of the
main conclusion occurs in any final theorem. Abstract helper inequalities
have concrete proven inputs at every use; the terminal objects are the
actual `Matrix (Fin 4) (Fin 4) ℂ`, Mathlib permanent/determinant, and usual
Euclidean row norms. Quantifiers are not replaced by a finite matrix sample.
