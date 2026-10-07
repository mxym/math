# math

Mathematical research manuscripts and supporting verification material maintained at **mxym/math**.

中文：本仓库收录数学研究稿、完整证明和可编辑源码。当前九份稿件涉及最优传输、二次整数阶中的有限步长图、精确维数的不可嵌入紧集、Erdős 相似性问题、投影体积的直积与 join 演算、单纯形刚性，以及非线性避让与光滑源的稳定性反例，并包含硬球气体的随机场路径极限。请从 [CONTENTS.md](CONTENTS.md) 进入各稿件。

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

The [five-page integrated-witness lower-end proof](notes/integrated-witness-simplex-stability/README.md) proves E(K,S) <= G_d* (a(K)-1/(d+1))^(1/d) for every full-dimensional compact convex body in d >= 3 and every maximum-volume inscribed simplex, using that simplex's own centroid. All constants and gates are explicit; no symmetry, smoothness, atomicity or uniqueness assumption is required. [PDF](notes/integrated-witness-simplex-stability/paper.pdf) · [Complete source archive](notes/integrated-witness-simplex-stability/source.zip). The separate [truncation obstruction](notes/simplex-truncation-stability/README.md) excludes powers above 1/(d-1); the gap between 1/d and 1/(d-1) remains unresolved.

The [44-page stronger symmetric upper-end proof](notes/stronger-symmetric-projection-stability/README.md) proves D(K,E_d)-1 <= min{d^12 delta^(1/(3d)), d^19 delta^(1/(3(d-1)))} for delta=1/2-a(K), every origin-symmetric full-dimensional compact convex body in d >= 3, and the entire affine class E_d of products of symmetric line and plane factors. Dimensions one and two have distance one. [PDF](notes/stronger-symmetric-projection-stability/paper.pdf) · [Complete source archive](notes/stronger-symmetric-projection-stability/source.zip). Constants are dimension-dependent. The interval between the proved 1/(3(d-1)) power and the obstruction ceiling 1/d remains open. Neither new proof uses a quantitative inverse-Minkowski theorem.

The [corrected historical upper-end article](notes/quantitative-symmetric-projection-stability-bibliographic-correction/README.md) is the active bibliographic reference for the earlier 1/(6d) theorem. Its [exact correction record](notes/quantitative-symmetric-projection-stability-bibliographic-correction/CORRECTIONS.md) preserves the mathematics while crediting Weil bodies, the matroid structure, lift-zonoid calculus and cap background, and treating the Böröczky–De comparison qualitatively. The [original note](notes/quantitative-symmetric-projection-stability/README.md), its PDF/source archive and all numbered version files remain byte-preserved. The supplied v4 attribution patch remains separate review material and is not applied. See the [integration and verification record](verification/2026-10-07-stronger-stability-integration/README.md) and [release manifest](releases/2026-10-07-stronger-stability-and-bibliographic-correction-v1.json). These are additive research supplements, without a novelty, priority, optimal-exponent, external peer-review or full-formalization claim.
