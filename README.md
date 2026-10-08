# math

## Exact triple-action spectrum, asymptotics, and orbital Chebyshev structure

The [permutation permanent / finite-group action research programme](notes/sharp-robust-permanent/README.md) has established a **sharp universal first-order theorem** for the action of \(S_n\) on three-element subsets:

\[
C_n^{(3)}=1-\frac{18}{n}+O(n^{-2}).
\]

Its [full analytic proof](notes/sharp-robust-permanent/paper.md#22-sharp-universal-first-order-asymptotics-for-all-three-subset-actions) combines an explicit global orbital dual bound and four exactly moment-matched positive probability constructions indexed by \(n\bmod4\). Independently, an exact finite classification now covers **every degree \(3\le n\le120\)**. The new degrees 24–120 have [97 fixed rational certificates](notes/sharp-robust-permanent/certificates/three_subset_n24_120.json), replayed through [1,489,083 exhaustive compressed cycle-type checks](notes/sharp-robust-permanent/code/check_three_subset_compressed_24_120.py). The [general three-cycle compression theorem](notes/sharp-robust-permanent/paper.md#20-an-exact-three-cycle-statistic-compression-theorem) explains why this is exhaustive.

The [higher-rank Bernstein theorem](notes/sharp-robust-permanent/paper.md#23-general-k-subset-orbital-bernstein-limits-and-a-chebyshev-research-direction) proves a uniform \(O_k(n^{-1})\) polynomial approximation for all fixed \(k\); its shifted Chebyshev mechanism explains the proven constants \(2,8,18\) at \(k=1,2,3\). The analogous \(2k^2\) law for \(k\ge4\) is a **conjecture**, not a published theorem. The [verification record](notes/sharp-robust-permanent/VERIFICATION.md) distinguishes analytic arguments, fixed exact finite certificates, independently replayed symbolic identities, and incomplete novelty/external-peer-review work.

# All-rank Johnson-action short-cycle reduction and exact four-subset certificates

The [fixed-k Johnson-action note](notes/johnson-short-cycle-spectrum/README.md) proves for every subset size k that the intersection-orbital statistics of S_n depend only on the counts of cycles of lengths at most k. It reduces the sharp marginal-preserving atom/TV optimization to an exact rational LP with O_k(n^k) types, proves the monotone subset-rank hierarchy, and certifies exact sharp four-subset constants for every n=11,...,50 (40 degrees). A [SHA-pinned independent VPS replay](notes/johnson-short-cycle-spectrum/VERIFICATION.md) validates 40 exact rational primal-dual certificates, 129,523 further reduced dual constraints for n=26,...,50, and 1,329 literal subset-image regressions, including negative controls. This is a rigorous model-assisted research note without an all-n four-subset closed formula, peer review, or novelty-priority assertion.


## Sharp period-1122 sieve jump at the norm-six prime step threshold

The [complete norm-six research note](notes/sqrt-minus-two-sqrt6-period/README.md)
proves that in Z[sqrt(-2)] the **least** finite principal-ideal
sieve period jumps sharply from 6 to **1122** as the genuine
Euclidean step radius reaches sqrt(6), remaining sharp until
sqrt(8). Its seven-generator norm sieve partitions **204,800**
allowed residues modulo 1122 into **6,688** finite components
of largest size 2,283. Every smaller scalar period is excluded
by 682 explicit nonzero-voltage paths. The true prime graph
contains a certified **90-prime** component, and every prime
component has at most 2,283 vertices. Independent standard-library
checker, complete literal witnesses, mutation tests and proof
roadmap are included. The true global prime maximum remains open;
no novelty, external peer-review or Lean claim is made.

## Exact three-subset optimality spectrum with rational proof certificates

The [permutation action manuscript](notes/sharp-robust-permanent/paper.md#19-a-complete-certified-three-subset-spectrum-through-degree-23) also determines the exact marginal-preserving atom-vs-total-variation coefficient for **every S_n action on 3-element subsets through n=23**. The nontrivial rank-four degrees n=6,...,23 are independently certified by [18 fixed rational primal-dual witnesses](notes/sharp-robust-permanent/certificates/three_subset_n6_23.json) and an [optimizer-free exhaustive checker](notes/sharp-robust-permanent/code/check_three_subset_certificates.py). The checker and published JSON passed a fresh isolated Windows replay from public GitHub main; see the [verification record](notes/sharp-robust-permanent/VERIFICATION.md). This is a complete exact **finite classification** only; no all-degree k=3 closed formula or priority certification is claimed.

## Universal orbital duality and exact symmetric-group two-subset law

The [permutation stability manuscript](notes/sharp-robust-permanent/paper.md) now proves, for **every n ≥ 4**, the exact optimal marginal-preserving atom/TV constant for the natural action of S_n on its 2-element subsets: (n²−2n+8)/[(n+2)(n+4)] for even n and (n²−n+4)/[(n+3)(n+4)] for odd n. The result gives an explicit matching primal probability construction and a direct all-n parity-dependent quadratic dual proof. It strictly improves the crude minimal-degree constant for every n ≥ 5. Its [exact checker](notes/sharp-robust-permanent/code/check_all_two_subset_actions.py) has passed for every conjugacy type of n = 4,...,40, but the mathematical proof is general, not a finite extrapolation.

The same manuscript proves a [universal orbital primal-dual theorem](notes/sharp-robust-permanent/paper.md#18-universal-orbital-primal-dual-theorem-for-finite-permutation-actions): for any finite permutation group action, the sharp local atom/TV coefficient is the optimum of a rational LP over conjugacy classes, dual to the oscillation of an orbital-count function. Earlier exact results for doubly transitive actions and the S5 edge action arise as rank-two/rank-three specializations. The [verification record](notes/sharp-robust-permanent/VERIFICATION.md) distinguishes analytical proofs, exact executable checks, and outstanding external review/novelty work.

## Exact radius-two jump in the Z[sqrt(-2)] prime graph

The [radius-two research continuation](notes/sqrt-minus-two-radius-two/README.md)
proves the maximum prime-component size jumps sharply from 3 to 7 at D=2;
for every real 2<=D<sqrt(6) exactly two 7-vertex components exist and
all others have at most two vertices. For ten coefficient steps,
period-six principal ideal sieves succeed **exactly when** they contain
(t),(1+t),(1-t), t=sqrt(-2); the minimum number of generators rises
from 2 to 3. Complete written proof, independent exact integer checker,
certificates, 2,048-subfamily audit and tamper tests are provided,
without external-referee or novelty claims.

## The original sharp simplex stability upper Main in Lean

The separate [complete upper-bound project](formalizations/sharp-simplex-upper-bound/README.md) proves Entry005.sharpMain : Entry005.sharpMainGoal with the unchanged original gSharp and exponent 1/(d−1). For every dimension d ≥ 3, actual compact convex body with nonempty interior, and every prescribed maximum-volume inscribed simplex S, the actual excess about S's original centroid is at most gSharp(d) times the actual entryDefect to power 1/(d−1). No geometric bridge remains as an assumed premise. The [exact theorem](formalizations/sharp-simplex-upper-bound/THEOREM.md) retains the full constant definitions and quantifiers. This is the audited 204-file input composition, including the missing source supplement, with all 123 mathematical modules unchanged. [Final-copy review](verification/2026-10-08-sharp-simplex-upper-bound/FINAL_COPY_AUDIT.md) · [Release manifest](releases/2026-10-08-sharp-simplex-upper-bound-v2.json) · [Frozen archive](releases/2026-10-08-sharp-simplex-upper-bound-source-v2.tar.gz). This package contains the original upper theorem, not a later improved-constant candidate; the matching lower proof is a separate project.

## Sharp Z[sqrt(-2)] prime graph and complete sieve classification

The [exact small-radius research note](notes/sqrt-minus-two-sharp-moats/README.md)
classifies the entire irreducible-element graph for every Euclidean step
radius D<2: two three-vertex paths for 1<=D<2, with every other
component isolated or a single edge, so the global optimum is exactly
3. For the full eight-neighbor step set it proves the minimum
principal-ideal scalar period is 6 and classifies **all** successful
optimal-period ideal lists, including composite generators. Twelve
short arithmetic certificates, an independent checker, mutation tests,
and an exhaustive 2,048-subfamily cross-check are available. This is
AI-assisted written mathematics, not external peer review or Lean.

## Sharp permutation-permanent robustness and group atom moduli

The [complete proof dossier](notes/sharp-robust-permanent/README.md) proves quantitative normalized permanent robustness for all arities, an exact sharp (S_3) stability radius at (p=2), and **exact radii on a nontrivial one-sided interval below 2** (with an existential lower endpoint). It classifies all endpoint equalities, gives an exact rational (p=5/2) counterexample to extending the singleton-radius formula above 2, and computes the (K_{3,3}) entropy reduction. An independent further theorem determines the optimal atom-vs-TV coefficient for **every finite doubly transitive permutation group**, sharply attained in symmetric, alternating and affine families. The [manuscript](notes/sharp-robust-permanent/paper.md) includes complete proofs, exact rational local margins and reproducible checkers; human peer review, priority assessment and a numerical lower endpoint for the exact interval remain open.

## Literal simplex-truncation sharpness in Lean

The separate [complete sharpness package](formalizations/simplex-truncation-sharpness/README.md) proves Entry005.truncationSharpnessGoal for the actual truncated body, geometric entryDefect, a simplex globally maximum among all inscribed affine simplices, and that simplex's original centroid. For every d ≥ 3 and α > 1/(d−1), arbitrarily small positive defects obstruct every proposed constant-C bound with exponent α for an exhibited maximizing simplex. The result establishes the exponent obstruction, not a claim about every maximizing simplex or a best-maximum choice. [Exact statement](formalizations/simplex-truncation-sharpness/THEOREM.md) · [Proof roadmap](formalizations/simplex-truncation-sharpness/PROOF_ROADMAP.md) · [Independent final-copy audit](verification/2026-10-08-simplex-truncation-sharpness/FINAL_AUDIT_REPORT.md) · [Release manifest](releases/2026-10-08-simplex-truncation-sharpness-v2.json). The exact 365-file source archive passed a fresh independent public-wrapper run: 125 rebuilt modules, 850 public declarations, and 1,849 owned roots replayed through a 55,163-declaration empty-kernel closure. This historical lower-bound checkpoint does not include the separate sharpMainGoal upper bound. No novelty or external human peer-review claim is made.

## Eisenstein irreducible graph: exact component maxima and sharp sieves

The [Eisenstein quadratic-order continuation](notes/eisenstein-prime-components/README.md)
proves that the six-unit and eight-neighbor irreducible-element graphs
in Z[omega] have unique largest components of **48 and 132** vertices.
Sharp principal-ideal scalar sieve periods are **6 and 546**, with
a complete four-generator classification even with composite
generators for the eight-neighbor graph.
An explicit full proof, 333 lower-period and 36 composite-rigidity cycles, complete quotient
partitions, prime-closure witnesses and an independent exact checker
are included. This is model-assisted, not external human review.

## Unified traditional proof of continuum-power avoidance

The [14-page revision-2 paper](notes/continuum-power-avoidance-unified/continuum-avoidance.pdf) gives the complete traditional proof of large closed sets avoiding a continuum of power asymptotics. For each prescribed nonempty countable log-syndetic family and 0 < ε < 1, one large-measure closed nowhere-dense periodic set works for every permitted positive real leading power and power-controlled remainder, with infinitely many distinct escaping outputs in every positive tail. The family is fixed before the set. The [reading guide and TeX source](notes/continuum-power-avoidance-unified/README.md) retain the exact corrected manuscript, the earlier defect and repair history, and a 20-step/57-declaration Lean correspondence. Both linked formalizations and all 12 external evidence destinations were verified on the repository. The independent model [revision-closure review](notes/continuum-power-avoidance-unified/review/REVISION2_CLOSURE.md) reports no remaining mathematical blocker; this is not external human peer review or novelty certification. [Publication manifest](releases/2026-10-08-unified-avoidance-revision2.json) · [Frozen source archive](releases/2026-10-08-unified-avoidance-revision2-source.tar.gz).

## Continuum powers with power-controlled remainders in Lean

The separate [complete Lean project](formalizations/continuum-remainder-avoidance/README.md) proves the stronger prescribed-family theorem. Fix a nonempty countable family of positive-real configurations with bounded logarithmic gaps and 0 < ε < 1. There exists one closed nowhere-dense one-periodic E, with Lebesgue measure > 1 − ε in every unit interval, that works simultaneously for every positive real leading exponent and remainder rate, nonzero signed coefficient, translation, and function with the stated eventual power remainder bound. Every positive input tail yields infinitely many distinct values outside E. A compact large-measure corollary is included. E is chosen after the family, not uniformly before all possible families. See the [exact statement](formalizations/continuum-remainder-avoidance/THEOREM.md), [final-copy audit](verification/2026-10-07-continuum-remainder-final-copy/FINAL_COPY_AUDIT.txt), [source archive](releases/2026-10-07-continuum-remainder-avoidance-source.tar.gz), and [release manifest](releases/2026-10-07-continuum-remainder-avoidance.json). The complete fresh-copy wrapper passed; its actual empty-kernel replay checks 34,923 endpoint-union and 35,620 all-safe closure declarations. The independent final-copy reviewer cross-checked those artifacts and logs without repeating the full build. This is model-assisted verification, with no novelty or external human peer-review claim. Earlier release entries below retain their historical scope.

## Full all-ratio affine-geometric avoidance in Lean

The separate [complete Lean project](formalizations/geometric-avoidance/README.md) proves the original all-real affine-geometric theorem: for every 0 < ε < 1, one compact E ⊆ [0,1] with Lebesgue measure > 1 − ε has arbitrarily late misses for every a qⁿ + b, simultaneously for all real a ≠ 0, b and 0 < q < 1. The exact frozen release passed an independent model-conducted [final-copy audit](verification/2026-10-07-geometric-avoidance-final-copy/FINAL_COPY_AUDIT.txt), including empty trust-level-zero kernel replay of the complete 34,771-declaration main closure. [Source archive](releases/2026-10-07-geometric-avoidance-source-v2.tar.gz) · [Release manifest](releases/2026-10-07-geometric-avoidance-v2.json). The historical 101-export checkpoint remains unchanged; this is a separate complete formalization of the original affine-geometric avoidance theorem. The stronger nonlinear-remainder theorem is outside this release. Standard Lean foundations and implementation trust remain; no novelty or external human peer-review claim is made.

[Transport programme: source overlap and target tails](notes/transport-source-tail-programme/README.md) connects manuscripts 001, 007 and 008 while preserving their separate versions and proof dependencies.

The [source-overlap synthesis](notes/transport-source-tail-synthesis/README.md) adds a complete six-page proof of the density-root Sobolev characterization of linear overlap for 1 < s < infinity, with pinned sources and reproducible checks. This characterizes the interpolation method; transport applications retain the separate potential estimate (P) and their moment/domain hypotheses.

Mathematical research manuscripts and supporting verification material maintained at **mxym/math**.

中文：本仓库收录数学研究稿、完整证明和可编辑源码。当前九份稿件涉及最优传输、二次整数阶中的有限步长图、精确维数的不可嵌入紧集、Erdős 相似性问题、投影体积的直积与 join 演算、单纯形刚性，以及非线性避让与光滑源的稳定性反例，并包含硬球气体的随机场路径极限。请从 [CONTENTS.md](CONTENTS.md) 进入各稿件。

## Complex three-row permanent–determinant theorem

The [exact norm theorem for every complex 3x3 permanent–determinant pencil](notes/complex-permanent-determinant/README.md) determines the least norm constant as the maximum of five explicit templates, which classifies precisely the complex determinant coefficients permitted by the sharp Euclidean permanent bound, yields a positive sharp absolute determinant term, classifies its complex equality cases and extends the exact three-row uniform-marginal robustness radius to arbitrary complex-valued L2 functions, and determines the **sharp amplification factor** for all such laws and their independent nonidentical-column tensor products. Its [Hermitian proof](notes/complex-permanent-determinant/PAPER.md) has a [replayable exact rational full-norm certificate](notes/complex-permanent-determinant/check_full_norm.py), a separate quadratic-field disk replay and complex matrix regression and a read-only CI workflow. This does not claim full n-row radius classification or external review.

## Sharp complex four-row permanent and determinant tradeoff

The [complete four-row theorem](notes/four-row-permanent-tradeoff/README.md) proves |per A|+c|det A| <= max(3/2,1+c) times the row Euclidean norm product for **all complex 4x4 matrices** and every real c>=0, including all equality cases and a quantitative pairwise stability deficit. Its algebraic method also proves an infinite family of sharp rectangular two-row inequalities, a full convex/Pareto endpoint theorem with exact all-real-power constants, and an [all-even Laplace/symmetric-tensor transfer](notes/four-row-permanent-tradeoff/EVEN_ROW_TRANSFER.md) identifying the remaining open 3x6 case. The [paper](notes/four-row-permanent-tradeoff/PAPER.md) further computes the exact complex-valued L2 norm and tensorization for the **parity-biased** S4 permutation subfamily, with sharp TV cutoff 1/4 within that subfamily only. [Exact polynomial identities](notes/four-row-permanent-tradeoff/check.py) and [tensor witness replay](notes/four-row-permanent-tradeoff/check_tensor.py) are supplied with read-only CI.

## Collection

| ID | Manuscript | Latest | Status |
| --- | --- | --- | --- |
| 001 | [Source regularity and sharp Brenier stability under target moment bounds](preprints/001-strongly-log-concave-brenier/README.md) | v5 | Research draft; source regularity and sharp target-tail distinctions |
| 002 | [Bounded step walks on irreducibles in quadratic orders](preprints/002-quadratic-order-moats/README.md) | v4 | Sharp F8 principal-sieve periods in Gaussian and Z[sqrt(2)] cases; all-order v3 preserved |
| 003 | [Compact Banach space obstructions with Assouad dimension two](preprints/003-assouad-two-zero-box/README.md) | v1 | Research draft |
| 004 | [A logarithmic upper Banach density criterion for the Erdos similarity problem](preprints/004-log-density-similarity/README.md) | v1.1 | Complete written proof draft; finite-cover verifier |
| 005 | [Projection-volume calculus, endpoint rigidity and spectral amplification](preprints/005-simplex-product-optimum/README.md) | v5 | Complete written proof; balanced-recursion optimum, symmetric equality classification and exact replay |
| 006 | [Modulus-controlled nonlinear avoidance and log-bi-Lipschitz profile extensions](preprints/006-modulus-nonlinear-similarity/README.md) | v2 | Complete written proof draft; profile invariance and inherited exact robust-cover replay |
| 007 | [Tail-sensitive convex-gradient interpolation and Brenier stability beyond bounded targets](preprints/007-tail-brenier-stability/README.md) | v2 | Complete written proof draft; smooth full-support counterexample |
| 008 | [Density overlap and a sharp boundary phase diagram for moment-controlled Brenier stability](preprints/008-density-overlap-phase/README.md) | v1 | Complete written proof draft; critical logarithm and exact multiscale checks |
| 009 | [Functional hard-sphere fluctuations on regular kinetic intervals](preprints/009-functional-hard-sphere-fluctuations/README.md) | v1 | Research draft; strong-dual functional limit with explicit imported inputs |

An [independent 005 proof and a stronger runner-up theorem](notes/independent-arity-simplex-recursions/README.md) establish a second exact proof of the all-arity homogeneous recursion classification and identify the unique second-best triple \((m,k,p)=(2,2,6)\), with a certified strict gap below it. The distinct first-place proof in the parallel supplement is cross-verification, not a second discovery; arbitrary product/join trees remain open.

A separate [nine-piece balanced-projector cover](notes/balanced_borsuk_slice.md) excludes one proposed Borsuk construction; it is not a solution of the eight-dimensional problem.

## Reading and verification

Each manuscript directory contains complete editable source (LaTeX or Markdown), reproduction instructions and upstream attribution. The arguments were developed with AI assistance and checked against explicit hypotheses and proof dependencies. **These are research manuscripts, not externally peer-reviewed or fully machine-formalized results.** See [verification/STATUS.md](verification/STATUS.md) for entries 001--003, the [additional audit record](verification/density-simplex-2026-10-07.md) for 004--005, and the [cross-audit and extensions record](verification/2026-10-07-cross-audit-and-extensions.md) with the [007 v2 audit](preprints/007-tail-brenier-stability/v2/PROOF_AUDIT.md) for the new additions. The exact finite checks do not replace the infinite analytic arguments. The similarity toy certificate is not a computed small-measure witness for the full theorem.

Several methods build on the public [OpenAI/math collection](https://github.com/openai/math), pinned at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The manuscripts distinguish inherited arguments from the extensions developed here. No affiliation with or endorsement by OpenAI is implied.

## Versions and disclosure

Versions are kept in separate `v1`, `v2`, ... directories. Corrections and extensions are recorded in [CHANGELOG.md](CHANGELOG.md); earlier versions remain accessible. The [v1 manifest](releases/2026-10-07-v1.json) and [v2 manifest](releases/2026-10-07-v2.json) record exact file hashes. Historical manifests must be checked at their corresponding publication commit, because the root catalogue evolves. The first research publication commit is [`4d718fe55d8b53eb8dd8634508c3297f0a978149`](https://github.com/mxym/math/commit/4d718fe55d8b53eb8dd8634508c3297f0a978149). The first complete source publication of entries 004 and 005 is [`e6c776cae39477baa4e1a03d59a1547417f1a68e`](https://github.com/mxym/math/commit/e6c776cae39477baa4e1a03d59a1547417f1a68e); their v1.1 number refers to private-draft revisions, not an earlier public version. Their [build workflow](.github/workflows/density-simplex-publication.yml) replays finite checks, compiles PDFs, records hashes, and preserves a versioned research release.

Entries 006 and 007 v1 are preserved in [modulus-tail-20261007-v1](https://github.com/mxym/math/releases/tag/modulus-tail-20261007-v1). The stronger 007 v2 is published separately as [tail-stability-20261007-v2](https://github.com/mxym/math/releases/tag/tail-stability-20261007-v2), with the first new extension source in `c8d4fa9d7afc28d10123e666af0dfcdfc3f2681d`. The older sources are not overwritten.

GitHub commit timestamps document this repository's disclosure history; they do **not** certify mathematical correctness or first discovery. Literature comparison continues separately, and no priority assertion is made.

## Rights and provenance

The upstream OpenAI material retains its Apache-2.0 license, reproduced in [third_party_licenses/openai_math_LICENSE.txt](third_party_licenses/openai_math_LICENSE.txt). See [NOTICE.md](NOTICE.md), the [additional provenance notice for 004--005](verification/density-simplex-2026-10-07.md), and the new manuscripts' explicit dependency notes. No additional license for newly authored material has been selected; do not infer one merely from the repository being public.

## Post-publication comparison

A [primary-literature comparison](comparisons/2026-10-07-primary-literature.md) records exact and partial overlaps found after the initial release. In particular, a nondegenerate semi-discrete W2 one-third estimate predates this collection, and W1 quarter-power estimates are not interchangeable with W2 one-third estimates. The note distinguishes these results from the current source and target scope; it does not certify priority.

The [parallel-work reconciliation](comparisons/2026-10-07-modulus-tail-reconciliation.md) identifies the overlap between 001 v3 and 007 v1 and the actual additional v2 results. An [additional model review of 004--005](reviews/2026-10-07-independent-model-review.md) reports exact replays and the known non-simplex rate comparison. It is not human peer review.

## Quadratic version 3

The [quadratic v3 manuscript and complete certificate data](preprints/002-quadratic-order-moats/v3/README.md) extend the finite certificate interface to individual nonzero nonunit principal generators, including ramified norm-prime and composite-norm cases. Exact quotient-component sizes and selected norm values sharpen the integer restoration bounds. Complete two-dimensional four-step and eight-step examples are supplied, together with an explicitly rejected candidate sieve.

The main all-quadratic-order existence theorem and its inherited analytic proof interface are unchanged. The 41 norm-prime tests, 24 general-principal tests, independent finite-lift/direct-multiplication checks, and 184-generator arithmetic checks are finite computational verification only. No unrestricted search implementation, practical-runtime guarantee, formal verification, or optimality claim is made. Exact changed-file hashes are recorded in the [v3 manifest](releases/2026-10-07-v3.json); cite the Git commit actually used.

## Transport version 3 and the smooth-source distinction

The [30-page transport manuscript](preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf) proves sharp one-third map stability on every fixed q>2 moment class for a full Gaussian source in dimension at least two, with the same positive rate for its specified full-support strongly log-concave class with globally bounded Hessian. Its general finite-q rate is (q−2)/(3q−2), sharp for the displayed conditioned-Gaussian and uniform-cube examples. At q=2 no uniform map modulus holds in dimension at least two, even with second moments exactly one. Dimension one remains isometric. See its [precise scope](preprints/001-strongly-log-concave-brenier/README.md) and [focused comparison](comparisons/2026-10-07-gaussian-finite-moments.md).

[007 v2](preprints/007-tail-brenier-stability/v2/README.md) shows that the slower finite-q exponent is not exclusive to support boundaries: one fixed positive C-infinity full-support strongly log-concave source also has that exact optimal power for every q>2. It separately extends the positive one-third result to the stated superquadratic sources with unbounded Hessian. These are compatible results, distinguished by quantitative translation regularity rather than qualitative smoothness alone.

## Nonlinear similarity extension

[006 v2](preprints/006-modulus-nonlinear-similarity/v2/README.md) extends the same robust-routing theorem from integer monomial leading terms to arbitrary prescribed countable families of log-bi-Lipschitz profiles. It covers positive power and power-log profiles and, by taking all rational powers and the standard power moduli, every convergent Puiseux germ with finite limit at zero. The endpoint restrictions remain: arbitrary C1 diffeomorphisms and flat smooth germs are not excluded.

## Transport version 4: focused logarithmic-moment continuation

The [13-page v4 paper](preprints/001-strongly-log-concave-brenier/v4/manuscript.pdf) proves the sharp full-Gaussian logarithmic-moment exponent min(1/3, beta/(beta+1)), including the loss-free beta=1/2 transition, and the exact order (q−2)^(-1/6) of the best finite-q one-third constant as q decreases to two. Sharpness and the beta=0 no-uniform-modulus obstruction are for dimension at least two; dimension one is isometric. Its stated full-support smooth strongly convex source extension does not include arbitrary hard boundaries.

This focused continuation explicitly uses the complete public v3 all-P2 potential theorem; it restates that input rather than re-proving its cell-calculus argument. [Version 3](preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf) remains the full record of the broader earlier potential, compact-source, tail, curve, and conditional-cell results. All historical files and independent entries are preserved. See the [precise dependency and scope](preprints/001-strongly-log-concave-brenier/README.md) and [v4 changed-file manifest](releases/2026-10-07-v4.json).

## Sharp permanent gap between nested and two-layer projection bodies

The [entry-005 permanent nesting theorem](notes/projection-persistent-nesting-gap/README.md) proves a **sharp dimension-uniform** multiplicative gap: for every `d>=55`, the ratio of the maximum normalized projection-body volume over *all* point-generated product/join trees to the maximum over *joins of simplex-product blocks* is at least the **exact d=55 value, greater than 1.007**, with equality **only** in dimension 55. The ratio is `>1.01` for every `d>=56`, and `>1.045` for every `d>=85`. The ratio additionally exceeds `(1009/1000)^(d-84)/45` for each `d>=85`, giving an explicit **exponential divergence** of sharp class maxima. This rigorously excludes *all subsequent dimensional re-entrance* of two-layer optimality after the first nesting threshold. [Complete paper](notes/projection-persistent-nesting-gap/paper.md) · [exact independent checker](notes/projection-persistent-nesting-gap/code/check.py) · [30-case public witness table](notes/projection-persistent-nesting-gap/results/finite_witnesses.tsv). The finite 55–84 bridge uses 11,234 new Pareto states and 2,837,399 exact comparisons; an analytically established two-layer upper envelope and eleven rational residue inequalities plus two exponential-rate comparisons prove the entire unbounded dimension tail. Neither individual sharp unrestricted-tree values beyond dimension 55 nor results for all convex bodies are asserted.

## First necessary nesting dimension: 55

The [exact dimension-55 first-crossover theorem](notes/projection-first-nesting-d55/README.md) strengthens the prior dimension-48 all-tree classification and dimension-85 nesting witness. For **every dimension 1–54**, the maximum normalized projection-body volume over all point-generated product/join trees has an attaining **two-layer** join-of-simplex-products body. At **dimension 55**, two independent Pareto-closure certificates prove the sharp all-tree value strictly exceeds the sharp two-layer value; consequently 55 is the **first dimension where nesting is necessary** to attain an optimum. Both rational fractions, explicit winning expression trees, 2,523,858 new full-tree operation checks and 430,360 two-layer checks are published with the [proof](notes/projection-first-nesting-d55/paper.md), [verifiers](notes/projection-first-nesting-d55/code/check_all_tree.py) and SHA-pinned reproducible data. The prior 85D strict witness remains valid but is no longer the earliest certified separation. The theorem is restricted to this recursive class, not all convex bodies or the asymptotic global constant.

## Strict nesting-depth separation in projection-body growth

The [two-layer spectrum and depth-separation theorem](notes/two-layer-projection-depth-separation/README.md) optimizes over **every** simplex-product block `T_p x T_q`: `(5,5)` uniquely maximizes its spectral rate, `(4,4)` uniquely maximizes its affine-defect rate, and any join of these blocks has asymptotic root rate at most `e*(189/128)^(1/11)` (sharp). A concrete **85-dimensional** body made by multiplying and rejoining earlier joins strictly beats **every** two-layer join-of-simplex-products construction, and the gap persists asymptotically. Both universal inequalities have analytic infinite-tail proofs plus [exact rational replay](notes/two-layer-projection-depth-separation/code/check.py). This supplies a structural transition beyond the sharp 1–48 finite results, but not an exact optimum or first crossover dimension in the full tree class.

## All-tree exact projection-body optima through dimension 48

The [entry-005 finite optima supplement](notes/exact-product-join-finite-optima/README.md) proves an exact Pareto-frontier recursion valid for **arbitrary** point-generated product/join trees (not only fixed-arity homogeneous recursions). A rational certificate determines the sharp normalized projection-volume maximum in every dimension 1–48, including the new exact dimension-48 value `105488578125/34359738368 > 3` times the simplex value, attained by `3*(T4 x T4)` and `2*(T5 x T5)` under affine joins. The [standalone proof](notes/exact-product-join-finite-optima/paper.md) establishes dominance/closure for all finite trees; a [separate exact checker](notes/exact-product-join-finite-optima/code/check.py) replays 6,494 states and 1,956,775 candidate comparisons and verifies rational witnesses in ordinary and optimized Python. Sharp values are **not** asserted above dimension 48, and no result for unrestricted convex bodies or optimal asymptotic rate follows.

## Independent-arity homogeneous product–join optimum

The [005 independent-arity supplement](notes/unbalanced-homogeneous-projection-recursion/README.md) closes a natural generalization of v5: for all positive integers `(m,k,p)`, the simplex-seeded recursion `K_{j+1}=(K_j^m)^{*k}` has a **unique** maximum asymptotic projection-volume root rate at `(2,2,5)`. Every competitor has log rate `<131/125`, strictly below the inherited winner `>2.8534`. The [complete proof](notes/unbalanced-homogeneous-projection-recursion/paper.md) excludes all infinite arity and seed tails; the [exact rational checker](notes/unbalanced-homogeneous-projection-recursion/checker.py) verifies 6,155 finite exclusions, endpoints and logarithm bounds in both Python modes. Unequal arities are now covered; arbitrary nonhomogeneous operation trees remain unresolved. This is model-assisted research, not human peer review, Lean verification or a novelty claim.
The subsequent [parallel independent-arity proof package](notes/independent-arity-simplex-recursions/README.md) gives an alternative derivation and exact checker of **the same** classification, not an additional distinct mathematical result; see the [cross-check](reviews/2026-10-07-independent-arity-parallel-audit.md).

## Projection geometry version 3

[005 v3](preprints/005-simplex-product-optimum/v3/README.md) extends lower-bound equality from polytopes to all convex bodies, proves qualitative affine stability and a sharp symmetric cone bound, and gives an explicit Cartesian-square spectral amplification theorem. The complete proof and exact replay were disclosed in `43bb307c76ec83d09feb2fe3aa74b2a40e3d2bdc`. The [read-only verification workflow](.github/workflows/projection-rigidity-exact.yml) replays rational checks and byte-identity comparisons; it does not rewrite published files. Historical v1.1 and v2 statements and their scopes are retained.

## Manuscript 001 version 5: source regularity

[Version 5](preprints/001-strongly-log-concave-brenier/v5/README.txt) combines the v4 Gaussian results with an exact minimum-density weight, fixed-source Sobolev little-o refinements, and stronger smooth-source target-tail obstructions. The root-density/Fisher criterion overlaps [008](preprints/008-density-overlap-phase/README.md) and is explicitly cross-credited, not counted twice. Its strict comparison with raw translation ratios and its endpoint qualifications are stated in full. The finite-q and stretched-exponential endpoint lower ratios tend to zero; the assertions are sharp powers, not matching positive endpoint constants or all-small-distance envelopes.

A [six-page supplement](notes/stretched-exponential-sharpness/README.md) proves matching stretched-exponential logarithmic lower bounds for fixed hard-boundary examples. It is a supplement to 001 and 007, not a new numbered paper. The [008 independent audit](reviews/2026-10-07-density-overlap-independent-audit.md) includes expanded exact replays. Historical sources remain unchanged.

## Critical boundary supplement: slowly varying density factors

The [six-page supplement](notes/critical-boundary-slow-variation/manuscript.pdf), with [complete source](notes/critical-boundary-slow-variation/manuscript.tex) and [scope/build information](notes/critical-boundary-slow-variation/README.txt), extends 008's critical multiscale construction to the specified positive C2 slowly varying factors. It proves a sharp implicit modulus for every sufficiently small target distance and a necessary iterated-logarithm correction at the displayed threshold. Within that exact source family, pure one-third stability is equivalent to the global density-root Sobolev condition; no arbitrary-source necessity claim is made.

The original 008 v1 is unchanged. The supplement explicitly imports its overlap interpolation and global mass-matching mechanism, and the 001 v3 all-P2 potential estimate. It is not a new numbered paper or a priority certification. See the [proof review](reviews/2026-10-07-critical-slow-variation-review.md) and [changed-file manifest](releases/2026-10-07-critical-slow-variation-v1.json).

## Functional kinetic limit and effective geometric rigidity

[Manuscript 009](preprints/009-functional-hard-sphere-fluctuations/README.md) supplies a complete 19-page functional hard-sphere fluctuation proof under its explicit pinned analytic inputs, with a strongly continuous tempered-distribution-valued Gaussian limit. It does not claim a quantitative CLT rate or new global Boltzmann regularity.

The [nine-page additive supplement to 005](notes/quantitative-projection-simplex-stability/README.md) gives an explicit dimension-dependent simplex-containment modulus for arbitrary convex bodies and every maximum-volume inscribed simplex. Its exponent and constants are deliberately conservative. The stronger planar Banach–Mazur bound is explicitly inherited from Böröczky’s prior work. No effective symmetric upper-end modulus or optimal spectral constant is claimed. [Source archive](notes/quantitative-projection-simplex-stability/source.zip).

The [005 v4 independent audit](reviews/2026-10-07-symmetric-projection-equality-review.md) verifies its separate symmetric equality classification. Historical version files are unchanged. The [publication manifest](releases/2026-10-07-functional-kinetic-and-rigidity-v1.json) records every changed file.

## Symmetric upper-end stability and restricted kinetic mean supplements

The [11-page upper-end supplement to 005](notes/quantitative-symmetric-projection-stability-bibliographic-correction/README.md) proves, for every centrally symmetric full-dimensional convex body in dimension d >= 3, the explicit bound D(K,E_d) - 1 <= d^15 (1/2 - a(K))^(1/(6d)). Here E_d is the entire affine product class of symmetric one- and two-dimensional factors. Corner-truncated cubes exclude every universal fixed-dimensional power above 1/d and every positive dimension-independent power; the historical 1/(6d) theorem is preserved; the stronger current modulus and remaining exponent gap are described below. The proof uses the pinned v2--v4 projection calculus and equality classification, separately from the lower-end simplex supplement and v5 recursion. [PDF](notes/quantitative-symmetric-projection-stability-bibliographic-correction/paper.pdf) · [Editable LaTeX source](notes/quantitative-symmetric-projection-stability-bibliographic-correction/paper.tex).

The [12-page virial/stress supplement to 009](notes/full-density-virial-stress/README.md) proves full-unit-amplitude first-order mean corrections for x·v and |x|² and convergence of a local momentum-balance defect to the classical collisional stress. It assumes smooth compact initial position and velocity support, a prescribed regular Boltzmann interval, and the explicit pinned H1--H6 history package. Its weighted passive-record extension is supplied in full; the imported history package is not independently reproved. The complete one-particle mean correction remains open, and no fluctuation theorem for these unbounded tests follows. [PDF](notes/full-density-virial-stress/manuscript.pdf) · [Editable source archive](notes/full-density-virial-stress/source.tar.gz).

Both are additive research supplements with precise public dependency maps, model-assisted proof audits, frozen PDF checks and offline verification. Neither is claimed as a Lean-formalized result, external peer review, or a novelty determination. See the [verification record](verification/STATUS.md#symmetric-upper-end-and-virialstress-supplements) and [changed-file manifest](releases/2026-10-07-symmetric-upper-and-virial-v1.json). Historical manuscript and certificate bytes are preserved; the separate Bellman audit summary only clarifies that its recursive class permits affine-isomorphic images on affine hulls.

## Mixed Bellman ceiling and simplex-truncation obstruction

The [11-page mixed Bellman supplement to 005](notes/mixed-bellman-product-join/README.md) proves Gamma_C <= exp(1049/1000) < 2.855 for the class generated from a point by finite products, joins and affine isomorphisms on affine hulls. Its exact mixed quadratic/quartic envelope improves the public quadratic ceiling while leaving the inherited lower bound 2.8534 and the unknown optimum unchanged. [PDF](notes/mixed-bellman-product-join/paper.pdf) · [Editable source archive](notes/mixed-bellman-product-join/source.zip) · [Separate independent audit and checker](verification/2026-10-07-mixed-bellman-independent-audit/README.md).

The [eight-page simplex-truncation supplement](notes/simplex-truncation-stability/README.md) proves exact truncation formulas and excludes any universal fixed-dimensional stability power above 1/(d-1), for d >= 3. This obstruction concerns both distance from the full simplex class and centroid containment using maximum-volume inscribed simplices. It does not prove a universal upper estimate at the endpoint power, and it does not close the gap to the previously released explicit lower-end modulus. [PDF](notes/simplex-truncation-stability/proof.pdf) · [Editable source archive](notes/simplex-truncation-stability/source.zip).

These additive supplements have explicit source maps and proof-audit limits. The truncation obstruction does not depend on an inverse-Minkowski positive stability extension. See the [verification record](verification/STATUS.md#mixed-bellman-and-simplex-truncation-supplements) and [release manifest](releases/2026-10-07-mixed-bellman-and-simplex-truncation-v1.json). Numbered manuscripts, Lean files, earlier certificates and unrelated supplements are preserved.

## Stronger endpoint stability and bibliographic correction

The [five-page integrated-witness lower-end proof](notes/integrated-witness-simplex-stability/README.md) proves E(K,S) <= G_d* (a(K)-1/(d+1))^(1/d) for every full-dimensional compact convex body in d >= 3 and every maximum-volume inscribed simplex, using that simplex's own centroid. All constants and gates are explicit; no symmetry, smoothness, atomicity or uniqueness assumption is required. [PDF](notes/integrated-witness-simplex-stability/paper.pdf) · [Complete source archive](notes/integrated-witness-simplex-stability/source.zip). The separate [truncation obstruction](notes/simplex-truncation-stability/README.md) excludes powers above 1/(d-1); the subsequently released [sharp endpoint note](notes/sharp-simplex-stability/README.md) attains 1/(d-1) in this same every-maximum-simplex centroid-containment class.

The [44-page stronger symmetric upper-end proof](notes/stronger-symmetric-projection-stability/README.md) proves D(K,E_d)-1 <= min{d^12 delta^(1/(3d)), d^19 delta^(1/(3(d-1)))} for delta=1/2-a(K), every origin-symmetric full-dimensional compact convex body in d >= 3, and the entire affine class E_d of products of symmetric line and plane factors. Dimensions one and two have distance one. [PDF](notes/stronger-symmetric-projection-stability/paper.pdf) · [Complete source archive](notes/stronger-symmetric-projection-stability/source.zip). Constants are dimension-dependent. The interval between the proved 1/(3(d-1)) power and the obstruction ceiling 1/d remains open. Neither new proof uses a quantitative inverse-Minkowski theorem.

The [corrected historical upper-end article](notes/quantitative-symmetric-projection-stability-bibliographic-correction/README.md) is the active bibliographic reference for the earlier 1/(6d) theorem. Its [exact correction record](notes/quantitative-symmetric-projection-stability-bibliographic-correction/CORRECTIONS.md) preserves the mathematics while crediting Weil bodies, the matroid structure, lift-zonoid calculus and cap background, and treating the Böröczky–De comparison qualitatively. The [original note](notes/quantitative-symmetric-projection-stability/README.md), its PDF/source archive and all numbered version files remain byte-preserved. The supplied v4 attribution patch remains separate review material and is not applied. See the [integration and verification record](verification/2026-10-07-stronger-stability-integration/README.md) and [release manifest](releases/2026-10-07-stronger-stability-and-bibliographic-correction-v1.json). These are additive research supplements, without a novelty, priority, optimal-exponent, external peer-review or full-formalization claim.

## Finite Lean verification and compact cubic kinetic coefficients

The standalone [Lean project](lean/README.md) now exports 101 checked source theorems: the original 68 finite/scalar exports, seven finite stochastic-matrix results and 26 projection-cap/constant lemmas. These counts include supporting lemmas. The actual-body cap/Hausdorff theorem retains its genuine uniform intrinsic projection-volume-deficit premise. The [final independent integration audit](verification/2026-10-07-lean101-independent-audit/README.md), [exact coverage](lean/coverage.json) and [completeness matrix](lean/COMPLETENESS_MATRIX.md) distinguish proved statements from five unproved Prop targets. The full sharp simplex and avoidance main theorems, actual simplex-volume/matrix bridge, threshold gate and truncation sharpness are not proved in this checkpoint. Lean 4.34.1 and all nine dependencies are pinned; checked logical axioms are restricted to propext, Classical.choice and Quot.sound. Two independent clean owned-module builds passed; the official compiler and pinned dependency cache remain trusted, with no separate external kernel checker. [Frozen source archive](releases/2026-10-07-lean101-verified-checkpoint.tar.gz) · [Release manifest](releases/2026-10-07-lean101-v1.json).

The separate [ten-page compact cubic hard-sphere supplement](notes/cubic-hard-sphere-contact/README.md) proves first-diameter expansions of the exact second and third activity coefficients for smooth compactly supported initial data. Incoming-contact convergence is uniform in incoming-flux L1 on every [delta,T] with delta > 0, and time-integrated through zero; the cubic mean remainder is uniform-in-time o(epsilon) in total variation. It uses classical isolated finite-particle flow/scattering facts, independently of the H1--H6 many-particle package. Gaussian-data, matched-layer and unsummed full-unit-amplitude extensions are excluded. [PDF](notes/cubic-hard-sphere-contact/manuscript.pdf) · [Editable source](notes/cubic-hard-sphere-contact/manuscript.tex) · [Exact-source sign-off](notes/cubic-hard-sphere-contact/audits/exact-source-signoff.txt).

Both additions preserve all historical manuscript and certificate bytes. See the [verification record](verification/STATUS.md#finite-lean68-and-compact-cubic-supplements) and [release manifest](releases/2026-10-07-lean68-and-compact-cubic-v1.json). The cubic model review is not external peer review; the finite Lean project does not formalize the whole geometric or kinetic papers.

## Sharp simplex endpoint, strict-domain calculus and positive sextic envelope

The [eight-page sharp simplex note](notes/sharp-simplex-stability/README.md) proves E(K,S) <= G_d^sharp (a(K)-1/(d+1))^(1/(d-1)) for every fixed integer d >= 3, every convex body K and every prescribed maximum-volume inscribed simplex S, using S's own centroid. Local, zero-defect and global cases have explicit dimension-dependent constants. Together with the preserved truncation family, the power 1/(d-1) is sharp for this stated class. The earlier 1/d proof remains unchanged. [PDF](notes/sharp-simplex-stability/proof.pdf) · [Editable proof](notes/sharp-simplex-stability/proof.tex) · [Complete source archive](notes/sharp-simplex-stability/source.zip).

The separate [12-page quantitative complete-calculus note](notes/complete-crouzeix-deficit/README.md) retains a nonnegative singular-vector deficit and proves the strict-domain factor 2/sqrt(1+min(mu^2,3)/M^2) for a finite matrix on its stated regular analytic convex enclosing domain. It also gives a Hilbert-space geometric certificate and a same-domain norm-perturbation bound. The gap below two can vanish in the outer limit. OpenAI's pinned direct manuscript already states complete constant two and supplies the imported Faber/ordered-product architecture and outer-limit recovery; this note claims neither a first resolution nor a new complete-two architecture. [PDF](notes/complete-crouzeix-deficit/paper.pdf) · [Editable source](notes/complete-crouzeix-deficit/research.tex) · [Source archive](notes/complete-crouzeix-deficit/source.tar.gz).

The [seven-page positive sextic Bellman note](notes/mixed-bellman-product-join/positive-sextic/README.md) sharpens the restricted growth bound to 2.8534 < Gamma_C <= exp(104867/100000) < 2.85386. C is generated from a point by finite Cartesian products, joins and invertible affine maps between full affine hulls. The inherited strict lower construction and unknown exact optimum are unchanged; no unrestricted convex-body or rank-dropping-map bound follows. [PDF](notes/mixed-bellman-product-join/positive-sextic/paper.pdf) · [Editable proof](notes/mixed-bellman-product-join/positive-sextic/paper.tex) · [Corrected complete certificate/audit archive](notes/mixed-bellman-product-join/positive-sextic/certificates-and-independent-audit.zip).

The [binary T5 limit companion](notes/mixed-bellman-product-join/sharpened-binary-lower/LIMIT_INTERVAL.md) now removes essentially all numerical uncertainty in the inherited lower orbit:
2.853465550695797 < Lambda_(2,5) < 2.853465550704, by Robbins/Machin/Taylor bounds and rigorous exact-rational logarithmic endpoint comparisons. Hence the same construction gives Gamma_C > 2.853465550695797. This does not prove optimality of the T5 orbit; the remaining gap to the positive-sextic Bellman ceiling is a global optimization gap. [Exact checker](notes/mixed-bellman-product-join/sharpened-binary-lower/check_limit_interval.py).

These additive analytic notes have independent model-conducted mathematical and final-copy reviews, scoped exact replay, complete source inventories and inspected PDFs. They are not whole-paper Lean formalizations, human peer review, novelty or priority determinations. The [verification record](verification/STATUS.md#sharp-simplex-strict-domain-and-positive-sextic-refinements) distinguishes fresh integration checks from retained historical full-tail evidence. The [release manifest](releases/2026-10-07-sharp-simplex-crouzeix-sextic-v1.json) binds all 78 package files and navigation edits. All historical proof, Lean and certificate files remain byte- and mode-preserved.

## Bounded-cluster avoidance, slow covering excess and arithmetic sieves

The [10-page bounded-cluster note](notes/bounded-cluster-avoidance/README.md) extends robust routing to uncountable pointwise selector families through bounded finite clusters. The fixed finite-cardinality bound, positive annular logarithmic upper Banach density and prescribed countable null-modulus/profile assumptions remain explicit. A successful whole cluster is chosen before independent allowed errors. This includes the stated finite-alphabet/profile switching corollary, with no arbitrary-C1, all-real-powers, unbounded-cluster or all-moduli theorem. [PDF](notes/bounded-cluster-avoidance/paper.pdf) · [Editable proof](notes/bounded-cluster-avoidance/paper.tex).

The separate [14-page critical covering gauge note](notes/critical-covering-gauge/README.md) constructs, for every finite-valued nondecreasing divergent gauge h:[1,infinity) -> [1,infinity) and every infinite-dimensional real Banach space, a countable compact subset with no bi-Lipschitz embedding into any finite-dimensional real normed space, upper box dimension zero and Assouad dimension exactly two. Its intrinsic covering bound is 350000 (R/r)^2 h(R/r), while its normalized exponent-two excess is unbounded. The complete supporting entry-003 proof and analytic appendix are included; dimension two is not claimed minimal or optimal. [PDF](notes/critical-covering-gauge/paper.pdf) · [Editable proof](notes/critical-covering-gauge/paper.tex) · [Two-note source archive](releases/2026-10-07-avoidance-covering-refinements-v1.tar.gz).

The [nine-page higher-degree arithmetic supplement](notes/higher-degree-rank-one-sieves/README.md) proves finite-state completion conditional on a supplied complete quotient with closed-walk voltage rank at most one in every component, and an all-degree irreducible restoration interface. In Z[theta], theta^3=2, its exact F6 and F8chain avoiding-component maxima are 6 and 56 at supplied period-ideal indices 30 and 330. The restored irreducible cardinality bounds are 4,825,576,145,682,469 and 46,926,635,792,162,881,985. These are cardinality bounds, not moat radii; no arbitrary-step, 26-neighbor or universal higher-degree moat theorem is asserted. [PDF](notes/higher-degree-rank-one-sieves/paper.pdf) · [Complete proof](notes/higher-degree-rank-one-sieves/paper.md) · [Source/certificate archive](releases/2026-10-07-higher-degree-rank-one-sieves-v1.tar.gz).

The two avoidance/covering notes retain [14 pinned source snapshots and exact provenance](notes/avoidance-covering-provenance/README.md), including OpenAI source credit and its Apache-2.0 license. The arithmetic [source map](notes/higher-degree-rank-one-sieves/SOURCE_MAP.md) distinguishes imported standard theorems, preserved certificate/original-checker bytes and strict public checker derivatives. Independent model-conducted mathematical and final-copy audits, finite exact replay, source/archive integrity and inspected PDFs support these releases. They are not whole-paper Lean formalizations, human peer review or novelty/priority determinations. The [verification record](verification/STATUS.md#avoidance-covering-and-higher-degree-arithmetic-supplements) and [release manifest](releases/2026-10-07-avoidance-covering-and-arithmetic-v1.json) state the exact scopes. All older proof, Lean and certificate paths remain byte- and mode-preserved.

## Continuum powers, semiconvex entropy and conserved quadratic fluctuations

The [11-page continuum-power avoidance note](notes/continuum-power-avoidance/README.md) proves, for every 0<ε<1, one closed nowhere-dense one-periodic set of measure greater than 1−ε in every unit interval that simultaneously avoids all positive real leading powers with positive-power remainders, for a prescribed countable family whose occupied dyadic logarithmic bins have bounded gaps near zero. Every sufficiently small image tail has infinitely many distinct misses. For {2⁻ⁿ}, it excludes all affine null geometric progressions simultaneously. Its negative answer concerns exactly the dated 17 October 2022 formulation of BGKMW Question 1; later-literature comparison remains incomplete, and no first-result or current-open claim is made. It does not cover arbitrary C¹/flat germs or every positive-upper-Banach-density configuration. [PDF](notes/continuum-power-avoidance/paper.pdf) · [Editable proof](notes/continuum-power-avoidance/paper.tex) · [Source archive](notes/continuum-power-avoidance/source.tar.gz).

The [nine-page semiconvex Gaussian entropy note](notes/semiconvex-gaussian-entropy/README.md) proves a sharp entropy-loss comparison under κ≥0 and Hess(−log q)≥−κI, finite entropy/score energy, smooth positive densities and an exponential-square moment, on the strict horizon z<1/κ (all z>0 when κ=0). It includes the conditional extension, sharp constants, a finite unweighted counterexample and an obstruction at the exact horizon. Its disclosed helper-domain correction is 0≤θ<a/2; downstream applications already use positive θ. This is not a general nonconvex logarithmic Sobolev inequality. [PDF](notes/semiconvex-gaussian-entropy/paper.pdf) · [Editable proof](notes/semiconvex-gaussian-entropy/entropy.tex) · [Source archive](notes/semiconvex-gaussian-entropy/source.tar.gz).

The [18-page conditional conserved-quadratic fluctuation note](notes/conserved-quadratic-fluctuations/README.txt) assumes smooth compact initial support, the operational history package H1–H6 and the existing exactly centered strong-Schwartz input F. It proves true-flow weak process convergence and first-moment transfer for the thirteen-dimensional conserved quadratic family, with pasted prelimit covariance convergence. The intrinsic moment corollary remains a weak-limit statement; true prelimit covariance and a full phase-space mean theorem are not established. [PDF](notes/conserved-quadratic-fluctuations/manuscript.pdf) · [Editable proof](notes/conserved-quadratic-fluctuations/manuscript.tex) · [Full source/evidence archive](releases/2026-10-07-conserved-quadratic-fluctuations-v1.tar.gz).

Independent model-conducted analytic and final-copy audits, ordinary/optimized finite replay and exact package integrity support these written results. The [verification record](verification/STATUS.md#continuum-powers-semiconvex-entropy-and-conserved-quadratic-fluctuations) and [changed-file release manifest](releases/2026-10-07-continuum-entropy-quadratic-and-transfer-v1.json) state the precise scopes. No complete Lean formalization, human peer review, journal acceptance or novelty/priority determination is claimed. All older proof, Lean, certificate and archive paths remain byte- and mode-preserved.

- [Complete base-similarity transfer literature comparison](notes/crouzeix-complete-transfer-comparison/README.md): a dated deduction combining Åhag–Czyż–Virtanen arXiv:2608.27346v3 with the attributed complete constant-two theorem. Broad strict-enclosure and perturbation conclusions follow from those inputs; the existing 18-file strict-domain proof/PDF/archive package is unchanged, and no first-result claim is made.

## Dimension refinements of sharp simplex stability

The [quadratic-dimensional refinement](notes/quadratic-dimensional-simplex-stability/README.md) is the strongest dimension bound in this repository for the sharp simplex endpoint: for every d >= 3, every full-dimensional convex body K and every prescribed maximum-volume inscribed simplex S, E(K,S) <= 4096 d² e(K)^(1/(d−1)), where e(K)=a(K)−1/(d+1) and E measures excess dilation about S's own original centroid. The complete written proof retains the sharp deficit exponent 1/(d−1); the optimal dimension order remains between linear and quadratic. [Complete theorem](notes/quadratic-dimensional-simplex-stability/QUADRATIC_DIMENSION_THEOREM.md) · [Source archive](notes/quadratic-dimensional-simplex-stability/source.zip).

The [earlier polynomial-dimensional method](notes/polynomial-dimensional-simplex-stability/README.md), with coefficient at most 2^20 d^6, is preserved as a companion proof and source of the shared weighted-anchor argument and square-pyramid linear lower bound. These are two stages of one additive refinement of entry 005, not two independent new papers. [11-page companion PDF](notes/polynomial-dimensional-simplex-stability/proof.pdf) · [Companion source archive](notes/polynomial-dimensional-simplex-stability/source.zip).

Both frozen packages passed independent model-conducted analytic and final-copy review, with exact source/integrity records and ordinary/optimized finite replay. See the [final-copy evidence](verification/2026-10-07-dimension-refinements-final-copy/README.md) and [release manifest](releases/2026-10-07-dimension-refinements-v1.json). No complete Lean formalization, human peer review, novelty or priority determination is claimed. Historical proofs and Lean files are preserved.

## Global orthogonal tensor rigidity

The [new tensor research note](notes/global-orthogonal-tensor-rigidity/README.md) gives an unconditional global square-root bound from contraction-commutator defects to orthogonal decomposition for every real symmetric tensor order p >= 3, including degenerate weights. It includes an exact sharp two-dimensional cubic formula, complete written proofs, four exact checkers and seven partial Lean algebra exports. Its separate entropy application remains conditional on an explicitly stated upstream remainder. Novelty and publication significance remain under investigation.

## Active research and literature screening

[Rank-six Ryser exploration](research/ryser-rank-six/README.md) supplies finite SAT search models, a solver-independent witness checker, geometric scouts and a complete integer enumeration excluding one restricted pencil template. No Ryser counterexample or unrestricted nonexistence theorem is claimed. The [initial literature comparison](research/novelty-assessment/2026-10-07-initial-screen.md), prepared with GPT-6 Luna at High reasoning effort, distinguishes known inputs, direct deductions, neighbouring results and unresolved novelty questions for the tensor note and other repository work.

## Sharp binary tensor bounds and optimal order growth

The [binary tensor companion](notes/sharp-binary-tensor-rigidity/README.md) determines the optimal growth order p^(1/4) of the best complete-commutator error constant in dimension two, and proves the exact quartic constant 3^(1/4)/sqrt(2) with full equality classification. A nine-page proof, exact standard-library checker, nine partial Lean exports and a frozen inventory are included. These results use no OpenAI theorem. The [binary benchmark comparison](research/novelty-assessment/2026-10-07-binary-odeco-benchmarks.md) and [dimension screening](research/novelty-assessment/2026-10-07-tensor-dimension-screen.md) record read literature and unresolved novelty questions; no priority or whole-paper formalization claim is made.

## Boundary-profile lower bounds for binary tensor rigidity

The [boundary-profile continuation](notes/boundary-profile-binary-tensor-rigidity/README.md)
turns every fixed finite edge-coefficient profile into an explicit
Gaussian/Fock variational lower bound for the sharp binary tensor constants.
An exact three-term profile proves
liminf C_p / p^(1/4) > 0.623586, improving both the original
2^(-3/4) lower constant and the concurrently published exact two-band
constant sqrt(2/7+sqrt(2)/14) = 0.6218758237... while leaving the current
2^(-1/2) upper constant open. The analytic profile limit has a complete written proof; two
standard-library exact implementations certify the displayed rational
corollary in ordinary and optimized Python. A concurrent mechanism theorem
shows the smaller two-band constant is optimal whenever the coordinate axes
remain local projection maxima; the new profile has
\(\gamma_1^2+\sqrt2\gamma_2=12346629/9765625>1\), so its improvement is
an explicit off-axis escape from that sharp subclass. No priority or external
peer-review claim is made.

The [Fock-profile ceiling continuation](notes/fock-profile-ceiling-binary-tensor-rigidity/README.md) then completes the natural finite-first-moment profile variational problem, proves attainment, raises the tensor liminf lower bound to \(>0.6238973\), and certifies \(0.6238973<\kappa_{\rm prof}\le\sqrt{779/2000}=0.624099351\ldots\). This upper endpoint is a ceiling only for the reflected boundary-profile mechanism; the true tensor upper constant remains \(2^{-1/2}\).

## Simultaneous harmonic-degree blocks

The [harmonic-dimension block note](notes/simultaneous-harmonic-degree-blocks/README.md)
extracts a quantitative consequence of OpenAI/math family 361. For every
block ratio beta < 3/2 and every sufficiently large starting integer k, one
near-Euclidean complete Ricci-nonnegative metric on R^3 violates the
Euclidean polynomial-growth harmonic-dimension comparison simultaneously
at every integer degree from k through floor(beta(k+1))-1. More generally,
an A-factor excess is obtained throughout the block whenever
A beta^2 < 9/4. The proof is exact and uses only degree monotonicity plus
the pinned upstream one-degree theorem. It does not give one fixed metric
with violations at infinitely many unbounded degrees.


## Improved binary tensor lower constant

The [two-band binary tensor companion](notes/binary-tensor-two-band-lower-bound/README.md)
gives, for every tensor order p >= 10, an explicit exact family whose own
normalized asymptotic constant is
\(\sqrt{(2+\sqrt2)/(2(3+\sqrt2))}=0.6218758\ldots\), improving the
original \(2^{-3/4}\) family. The projection maximum and Gram residual are
proved in closed form; an exact standard-library Q(sqrt(2)) checker supplies
diagnostic replay. The
[boundary-profile continuation](notes/boundary-profile-binary-tensor-rigidity/README.md)
subsequently raises the overall rigorous liminf lower bound above 0.623586.
The upper constant \(2^{-1/2}\), convergence question and optimal leading
constant remain open.

## A nineteen-edge necessary bound for rank-six Ryser

The [rank-six degree theorem](research/ryser-rank-six/NINETEEN_EDGE_BOUND.md) proves that every intersecting six-partite six-uniform hypergraph with at most eighteen distinct edges has a five-cover, without bounding the vertices in each part. A six-page proof, exact replay of all 134,596 final degree-pattern combinations, a separate scalar certificate and three partial Lean exports are included. Thus a rank-six counterexample would need at least nineteen edges. The unrestricted conjecture remains unresolved here; the [source comparison](research/novelty-assessment/2026-10-07-ryser-nineteen-edge-precedent.md) distinguishes this partite bound from the general cover-number problem and records finite literature scope. Root-flower, private-neighbour and first-case edge-criticality constraints support continued witness searches.

## Partite intersecting cover-number lower bounds

The [all-rank partite cover note](notes/partite-cover-number-lower-bound/README.md) proves m >= 5 tau(H) - 7r/4 - 5 for every finite simple intersecting r-partite r-uniform hypergraph, r >= 2. Thus the minimum edge count under tau >= r-1 satisfies f(r) >= ceil(13r/4 - 10). The six-page complete proof includes the explicitly attributed Sivashankar degree-three lemma and a separate independent elementary branch with coefficient 511/160. Exact checkers and nine partial Lean scalar exports are supplied. This is stronger than the directly applicable 293/96 coefficient in the literature checked; no priority, full Lean formalization or resolution of Ryser's conjecture is claimed.

## Saving-sensitive partite cover continuation

The [linearization continuation](notes/partite-cover-number-linearization/README.md) strengthens the same cover-number programme: for every delta > 0, all finite simple intersecting r-partite r-uniform hypergraphs satisfy m >= 5 tau(H) - (5/3 + delta)r - C_delta. Consequently f(r) >= (10/3 - epsilon)r for sufficiently large r whenever its class is nonempty. The seven-page proof couples part-cover saving to the retained linear four-block count, uses the attributed Kahn edge-colouring theorem and includes the inherited degree-three lemma's full proof. Exact replay, eight partial Lean scalar exports and explicit dependency limits are supplied. The preceding finite 13/4 package is preserved. No numerical asymptotic threshold, full formalization, priority or Ryser resolution is claimed.

## Intersection structure in the same partite cover programme

The [intersection-excess continuation](notes/partite-intersection-defect-cover/README.md) proves a global cover inequality with an explicit penalty 10 I(H)/r, where I(H) sums |A intersect B|-1 over unordered edge pairs. Linear and near-linear families with tau >= r-1 have an asymptotic edge lower coefficient (5 sqrt(17)-7)/4 = 3.403882..., and any such family with edge/rank ratio tending to 10/3 must have liminf I(H)/r² >= (15 sqrt(17)-61)/120 > 0. The seven-page full deduction, exact weighted linearization checker and six partial Lean scalar exports identify all inherited colouring and degree-three inputs. This is a structural continuation of the preceding bounds, with no optimality, priority, numerical asymptotic threshold or Ryser resolution claimed.

## Superlinear edge necessity for near-linear Ryser equality families

**Prior-work correction:** [Kahn 1994 and a short pruning argument](research/novelty-assessment/2026-10-07-kahn-prior-work-addendum.md) already imply the superlinear necessity in this restricted class. The note below is an independent deduction, not an original solution of that consequence.

The [arbitrary-degree replication theorem](notes/superlinear-near-linear-partite-cover/README.md) proves that intersecting r-partite r-uniform families with tau >= r-1 and intersection excess I(H)=o(r²) must have |E(H)|/r tending to infinity. In particular f_linear(r)/r tends to infinity, taking empty classes as infinity. A fixed budget |E(H)| <= C r forces the linear cover gap tau <= (1-1/(2(C+1)))r + O_C(1). The complete five-page deduction uses the published Kahn bounded-rank small-codegree theorem with explicitly checked parallel-copy conventions; all fixed-parameter constants and orders of limits are specified. Exact replication replay and six partial Lean scalar exports accompany the proof. This strengthens the same programme to a structural limit theorem, but supplies no explicit growth rate, all-rank existence, priority claim or unrestricted Ryser solution.

## Sparse near-linear cover law without parts

[Kahn's prior harmonic bound](research/novelty-assessment/2026-10-07-kahn-prior-work-addendum.md) and its near-linear corollary are distinguished from the stronger piecewise bound, finite penalty and equality statements below. Historical novelty of those stronger statements remains under review.

The [eight-page cover-law continuation](notes/sparse-near-linear-cover-law/README.md) drops the partite assumption. For intersecting r-uniform families with bounded m/r and I(H)=o(r²), it proves tau/r <= h(m/r)+o(1), where h is the piecewise linear interpolation of a/(a+1) at nonnegative integers a, and h(x) <= x/(1+x). Thus near-linear Erdős–Lovász families with tau/r tending to one also require m/r tending to infinity. Integer equality forces degree variance sum_v(degree(v)-a-1)²=o(r²); affine-space examples attain prime-power endpoints. Every noninteger ratio greater than one has an explicit positive gap below the envelope, whose best size is unresolved. The finite theorem supplies an explicit excess coefficient, a complete proof, exact nonpartite diagnostics and fourteen partial Lean exports. Its external colouring input and limited literature comparison are distinguished from the new deduction; no general nonlinear resolution, priority or full formalization is claimed.

## Twenty-edge necessary condition for a rank-six Ryser counterexample

The [twenty-edge obstruction](notes/rank-six-twenty-edge-bound/README.md) proves that every intersecting six-partite six-uniform hypergraph with at most nineteen edges has a five-cover. Its five-page complete proof uses four-vertex cover budgets and a small intersection-excess obstruction; the known at-most-twelve four-cover theorem is fully proved in an attributed appendix. Exact degree/overlap replay and nine partial Lean scalar exports accompany it. A twenty-edge counterexample, if one exists, has at most eight vertices in each part and maximum degree seven. A bounded exploratory SAT run is recorded separately and supplies no exclusion certificate. The prior nineteen-edge package is preserved; the unrestricted rank-six problem remains open.

## Universal fractional cover envelope and design equality

The [fractional-cover continuation](notes/fractional-intersecting-cover-envelope/README.md) proves an unconditional finite edge/rank bound for fractional vertex covers of all intersecting r-uniform hypergraphs. Equality is characterized exactly by Steiner-design duals. For c between k-1 and k, the limiting bound phi(c)=k(k-1)/(k²+k-1-c) is strictly below both h(c) and c/(c+1) at noninteger c>1; a further explicit positive gap below phi is proved there, while that historical package left the actual frontier unresolved; the [sharp-frontier continuation](notes/sharp-fractional-cover-frontier/README.md) below now determines it at every finite real ratio. The proof uses maximum dual weight and threshold counting, with finite LP duality explained in an appendix. Ten exact primal/dual certificates and twelve partial Lean algebra exports are supplied. This is a fractional theorem; no corresponding integer bound, priority or full formalization is asserted.

The [active Kahn triple-intersection study](research/kahn-triple-intersection/README.md) records the exact 4/3 triangle obstruction to rounding an arbitrary optimal fractional cover, with explicit attribution to Kahn's existing mechanism. A local surplus inequality for Kahn's particular weights is proved, while the global rounding step remains missing. This is an obstacle and route record, not a solution or a claim that the conjecture is still unresolved in all subsequent literature.

The [same-day source-status addendum](research/kahn-triple-intersection/SOURCE_STATUS_ADDENDUM.md) identifies Kayll's existing theorem resolving Kahn 5.6. Its local matching-polytope condition cannot be replaced by the recorded cover-cost surplus; the general 5.5 route remains unproved here.

## Fractional-extremizer stability and integer recovery

The [five-page design-stability continuation](notes/fractional-design-stability/README.md) proves a finite deletion estimate: at m=(k-1)r+1, deficit d=m/k-tau* permits at most 4k²(k+1)d deletions to obtain maximum degree k and excess I<=q s/2. The dependence on d has the right order, with an exact 2d deletion example for k=2. At every fixed positive integer ratio m/r->a, fractional extremality tau*/r->a/(a+1) holds iff o(r) edge deletions leave maximum degree a+1; the core is nearly a Steiner design. Kahn's attributed small-intersection corollary then gives tau/tau*->1, although the original family's I/r² can diverge. Seven Lean exports verify the actual finite incidence extraction and converse feasible weights; limits, LP duality, degree/excess counts and imported rounding are written proofs, not a whole-paper formalization. Exact certificates, independently exhausted deletion minima, pinned dependencies and a frozen inventory are supplied. Novelty remains under comparison, with no unrestricted Ryser solution or priority claim.

## Sharp fractional frontier at every finite real ratio

The [eight-page sharp-frontier proof](notes/sharp-fractional-cover-frontier/README.md) determines the exact limiting fractional cover value for all simple intersecting rank-bounded hypergraphs with m/r->c: psi(c)=c/2 for c<=1, and psi(c)=max{a/(a+1),c/(a+2)} for a<=c<=a+1. Uniform constructions attain every real ratio; each interval has a plateau and a linear ramp. An explicit affine partial-pencil construction and private padding attain the complete fractional curve within partite uniform families for c in [0,4], with exact equality of their integer and fractional covers. The elementary finite bound tau*<=max{((k-1)r+1)/k,m/(k+1)} needs no partite or intersection-size condition. Wilson's attributed design existence theorem and Kahn's attributed 1994 covering corollary are used only in the sharpness constructions. On a strict ramp, exact equality holds iff maximum degree is at most k+1; an explicit deficit deletion bound gives the asymptotic iff for c in (k-1/k,k]. Nine Lean exports include the full finite hypergraph-incidence argument for every feasible dual vector, rather than only scalar elimination. LP duality, construction inputs, degree extraction and limits remain written/imported proofs. Exact primal/dual certificates, negative controls, pinned dependencies and a frozen inventory are supplied. This is not a general integer-cover result, and historical novelty remains under comparison.

## Complete fractional matching spectrum for arbitrary bounded packing

The [six-page bounded-packing spectrum](notes/fractional-matching-spectrum/README.md) extends the preceding intersecting law to arbitrary simple hypergraphs with matching number at most any fixed s. Its exact limiting curve is Psi_s(c)=max{sum_i psi(c_i): c_i>=0, sum_i c_i=c}. The finite bound tau*<=r Psi_s(m/r)+s/2 has an optimal universal additive error; disjoint components of a common uniform rank attain every fixed-s asymptotic value. A finite closed formula eliminates continuous optimization. When both rank and matching number diverge, the sharp normalized frontier is the concave interpolation h of a/(a+1), with a uniform spectral error below 1/(2s). The upper bound uses a maximum-weight greedy anchor partition and no external existence theorem. Wilson and Kahn are named sharpness inputs, with Wilson alone sufficient at integer endpoints and for the diverging-matching limit. Three additional Lean exports prove the actual anchor bound and half bound using the byte-identical nine-export predecessor; the greedy and asymptotic steps remain complete written proofs. Exact convolution diagnostics, primal/dual certificates, exhaustive small matching counts, source lineage and a frozen inventory are supplied. No integer-rounding or general weighted nonuniform FKS solution or historical priority is claimed.

## Diffuse optimum certificates and integer recovery with small triple intersections

The [six-page diffuse-cover continuation](notes/diffuse-fractional-cover-rounding/README.md) proves a finite coordinate bound for a selected optimal fractional cover: with maximum vertex degree D>=3 and Delta=(D-1)m-D(D-2)r-D>0, an optimum of value m/D exists whose weights are at most 1/ceil(Delta/[D(D-2)]). A three-complement repair and minimax argument prove this without an intersection-size assumption. Combining the diffuse certificate with a proved local matching-polytope condition, Edmonds's theorem and Kayll's attributed rounding theorem gives tau=m/D+o(r) when maximum triple intersection is o(r) and m/r tends to c in (D-1-2/[3D(D-2)+2(D-1)],D-1]. For D=3 this is (24/13,2]; for D=4 it is (44/15,3]. Pair intersections may be of order r. The same conclusion applies after o(r)-edge extraction to fractional extremizers in those intervals. Six partial Lean exports, exact repairs across ten degrees, rational primal/dual and local matching certificates, negative controls and a frozen inventory are supplied. The minimax existence, imported theorems and asymptotic deductions are complete written proofs rather than a full Lean formalization. The entire strict ramp and general Kahn 5.5 question are not resolved, and no historical priority is claimed.
