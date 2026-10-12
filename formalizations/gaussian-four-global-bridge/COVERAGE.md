# Paper → required lemma → Lean proof correspondence

Audited main base: `9526e94c7570e49f4376ab5e2fc29e58d28027e1`.
Reference: `research/gaussian-balanced-four-global/paper.md` and `AUDIT.md`.
No AGENTS.md was found in that checkout. The pre-existing algebra-only checks
are not counted as proof of analytic inputs.

| Paper component | Required actual mathematics | Coverage of this package |
|---|---|---|
| Section 2, moment definitions | Integrable fractional labels, zero Gaussian mean, actual Bochner moments | Reused `GaussianPartition`; original measurable cells in `GaussianSetPartitions` |
| Section 2, prices | Minima, derivatives, balanced masses, unique gauge prices, primal/dual equality | Reused nine-module actual-measure package; distinctness explicitly required where winning labels are used |
| Lemma 2 | Value continuous and homogeneous on the closed covariance cone | Actual score-level continuity and homogeneity proved, including collisions; Gram-distribution invariance proved; the selected covariance square-root parameterization still missing |
| Lemma 3, (4)–(6) | Actual facet flux B=LM, price Hessian L, covariance derivative | Missing |
| Lemma 4, (8)–(9) | Uniform separation of actual moment pairs | Proved by `balanced_winning_moment_separation`; general fractional pair theorem included |
| (10), price bound | Sharp pairwise quantile bound | Missing; a coarser actual gauge-price bound is proved by `balanced_price_bound` |
| Lemma 5, first paragraph | Actual mass and first-moment limits with separated limiting rows | Proved by `tendsto_winning_setIntegral`, `tendsto_winning_mass`, `tendsto_winning_moment`, `balanced_winning_limit` |
| Lemma 5, facet paragraphs | No codimension-one triple tie; facet areas and L converge | Missing |
| Lemma 6 | Exclude balanced rank-one/rank-two self-moment diagrams with L≤P | Missing; unrestricted three-cell bound and Gaussian isoperimetry not imported as axioms |
| Lemma 7 | Exact tetrahedral actual value and strict constrained local maximum | Missing; the proved separation constant is not this sharp constant |
| Lemma 8 | Four-cell Gaussian multi-bubble/perimeter input and interior critical-value bound | Missing |
| Lemma 9 | Upper-normal mountain pass and boundary-respecting deformation | Missing |
| Theorem 10, (20)–(22) | Spectral normal-cone relation and actual residual estimate | Missing |
| Theorem 10, (23) | Actual self-moment limit from converging balanced diagrams and residuals | Proved by `residual_limit_injective`, `residual_limit_multiplier_pos`, `balanced_residual_limit`, `balanced_limit_self_moment`; production of the sequences is not proved |
| Theorem 10 | Global covariance sharp bound and unique optimizer | Missing |
| Theorem 1 reduction | Arbitrary balanced fractional/set partition → centered trace-one score problem | Proved by `sqrt_energy_le_normalized_value` and `SetPartition.normalized_reduction` |
| Theorem 1 equality | Own-score dual equality forces hard winning labels | Proved, with equality and distinctness explicit, by `winning_labels_of_energy_value_equality` |
| Theorem 1 geometry | Tetrahedron necessary and sufficient, a.e. orthogonal/relabel/cylindrical classification | Missing; null-modification moment invariance and isometric score-value invariance alone are not the classification |

The new proof root list has 85 theorem/lemma names, not 85 independent major
results. The combined 135-root audit includes 50 existing roots. The precise
module import graph is `proof-dependencies.dot`; the full declaration graph is
represented by the replay closure list when an actual run completes.

The available three-cell independent development is on branch
`research/gaussian-three-cell-20261008`, fixed commit
`da16f54190bb53651a78640bd94a30a5c2cc9e08`; its directory is absent from main at
the audited base. Its documented equal-mass endpoint cannot simply substitute
for the unrestricted three-cell bound needed after merging cells in Lemma 6.
It has not been imported or independently reverified for this package.
