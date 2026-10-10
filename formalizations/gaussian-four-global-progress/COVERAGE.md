# Paper → necessary mathematical statement → Lean coverage

Audited base: main `9526e94c7570e49f4376ab5e2fc29e58d28027e1`.
Reference: `research/gaussian-balanced-four-global/paper.md` and its `AUDIT.md`.
No AGENTS.md was found in that checked-out repository.

| Paper component | Actual mathematical requirement | Current coverage |
|---|---|---|
| Section 2, first moments | Integrable labels and vector moments; zero total moment | Upstream `GaussianPartition` |
| Section 2, prices | Existence, actual masses, uniqueness, primal/dual attainment | Upstream nine-module actual-measure package; distinct scores only for deterministic winners |
| Lemma 2 | Continuous covariance value; square-root scaling, including singular Q | Covariance formulation not proved in this checkpoint |
| Lemma 3, (4)–(6) | Actual facet flux B=LM; price Hessian L; smooth covariance derivative | Missing |
| Lemma 4, (8)–(9) | Uniform actual moment-pair separation | `balanced_winning_moment_separation`; more general fractional theorem included |
| Lemma 5, first paragraph | Mass/moment limits for separated scores | `tendsto_winning_setIntegral`, `tendsto_winning_mass`, `tendsto_winning_moment`, `balanced_winning_limit` |
| Lemma 5, remaining paragraphs | No codimension-one triple tie; facet areas and L converge | Missing |
| Lemma 6 | Exclusion of self-moment rank-one/rank-two diagrams with L≤P | Missing; includes unrestricted three-cell bound and actual Gaussian isoperimetry |
| Lemma 7 | Exact tetrahedral value and strict constrained local maximum | Exact constant evaluation and analytic Hessian missing |
| Lemma 8 | Four-cell Gaussian multi-bubble perimeter lower bound; critical-value bound | Missing, not replaced by an axiom |
| Lemma 9 | Projection-flow mountain pass with the upper-normal sign | Missing |
| Theorem 10, (20)–(22) | Spectral normal-cone relation and actual residual estimate | Missing |
| Theorem 10, (23) | Noncollision and balanced self-moment limit from convergence and residuals | `residual_limit_injective`, `residual_limit_multiplier_pos`, `balanced_residual_limit`, `balanced_limit_self_moment` |
| Theorem 10 | Global covariance sharp bound and unique optimizer | Missing |
| Theorem 1 | All measurable/fractional partitions, sharp constant, full equality classification | Missing; upstream dual equality alone is not geometric classification |

## Non-circularity

No theorem assumes the tetrahedral bound, covariance maximality, a perimeter
comparison, a Gaussian isoperimetric theorem, a deformation flow, or a facet
Hessian as an unnamed abstract property. Boundary-transfer theorems state their
sequence, balancing, convergence and residual hypotheses in their Lean types.
They do not prove that the mountain-pass construction produces such a sequence.

The available independent three-cell development is on branch
`research/gaussian-three-cell-20261008`, fixed commit
`da16f54190bb53651a78640bd94a30a5c2cc9e08`; its project directory is absent from
main at the audited base. Its documented **equal-mass** endpoint cannot simply
be substituted for the **unrestricted** three-cell bound needed after merging
cells in Lemma 6. It has not been imported into this package.

The imported Milman–Neeman and classical Gaussian isoperimetric results in the
written paper are not Lean premises here. Their missing formalizations remain
substantive gaps, not administrative finishing work.
