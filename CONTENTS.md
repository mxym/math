# Manuscript catalogue

| ID | Manuscript | Latest | Status |
| --- | --- | --- | --- |
| 001 | [Source regularity and sharp Brenier stability under target moment bounds](preprints/001-strongly-log-concave-brenier/README.md) | v5 | Research draft; source regularity and sharp target-tail distinctions |
| 002 | [Bounded step walks on irreducibles in quadratic orders](preprints/002-quadratic-order-moats/README.md) | v3 | Research draft |
| 003 | [Compact Banach space obstructions with Assouad dimension two](preprints/003-assouad-two-zero-box/README.md) | v1 | Research draft |
| 004 | [A logarithmic upper Banach density criterion for the Erdos similarity problem](preprints/004-log-density-similarity/README.md) | v1.1 | Complete written proof draft; finite rational-cover checker |
| 005 | [Projection-volume calculus, endpoint rigidity and spectral amplification](preprints/005-simplex-product-optimum/README.md) | v4 | Complete written proof; symmetric equality classification, qualitative stability and exact finite checks |
| 006 | [Modulus-controlled nonlinear avoidance and a differentiability boundary for null patterns](preprints/006-modulus-nonlinear-similarity/README.md) | v1 | Complete written proof draft; robust finite-cover checker |
| 007 | [Tail-sensitive convex-gradient interpolation and Brenier stability beyond bounded targets](preprints/007-tail-brenier-stability/README.md) | v2 | Complete written proof draft; smooth full-support sharpness and exact algebra checks |
| 008 | [Density overlap and a sharp boundary phase diagram for moment-controlled Brenier stability](preprints/008-density-overlap-phase/README.md) | v1 | Complete written proof draft; sharp critical logarithm and exact multiscale cell checks |

All entries contain full proof drafts. This catalogue does not claim novelty certification or formal proof completion. The verification scopes of 004--005 are recorded [separately](verification/density-simplex-2026-10-07.md); their first complete source publication is commit `e6c776cae39477baa4e1a03d59a1547417f1a68e`.

For 006--007 see the [cross-audit](verification/2026-10-07-cross-audit-and-extensions.md), [007 v2 proof audit](preprints/007-tail-brenier-stability/v2/PROOF_AUDIT.md), and [parallel-work reconciliation](comparisons/2026-10-07-modulus-tail-reconciliation.md). Overlapping target-tail results from 001 v3 and 007 v1 are not counted as separate new project results. The additional smooth full-support counterexample and superquadratic-source statements are in 007 v2. The 006 statement excludes nonflat smooth germs, not all C1 or flat-smooth maps.

For 008 see its [proof audit](preprints/008-density-overlap-phase/v1/PROOF_AUDIT.md), [scope comparison](comparisons/2026-10-07-density-overlap-phase.md), and [versioned release](https://github.com/mxym/math/releases/tag/density-overlap-20261007-v1). First complete source: `f2398f916f6ae9a46b814522b3e1d34124b74f19`; compiled and replayed publication snapshot: `b6986ffce1448abf09db40b32b3158ab603c428a`. Its exact classification is restricted to the displayed boundary-vanishing source family. Upper bounds explicitly use the pinned potential theorem of 001 v3; independent interpolation and lower constructions are proved in 008. The critical lower bound allows a growing number of target atoms.

## Notes

[A nine-piece cover of a balanced projector slice](notes/balanced_borsuk_slice.md) excludes one specific eight-dimensional Borsuk route. It is not a claim about all eight-dimensional sets.

## Supporting comparisons

- [Geometry: exact dimensions, inherited properties, and earlier work](comparisons/2026-10-07-geometry-dimensions.md). The geometry manuscript remains v1.
- [Gaussian finite-moment stability: focused literature comparison](comparisons/2026-10-07-gaussian-finite-moments.md). Comparison for the transport v3 finite-moment extension.
- [Additional model review of 004--005](reviews/2026-10-07-independent-model-review.md), including independent exact replays and the known non-simplex rate comparison.
- [Nonlinear avoidance and transport-tail reconciliation](comparisons/2026-10-07-modulus-tail-reconciliation.md), distinguishing inherited, overlapping, and additional results.
- [Density overlap and boundary criticality](comparisons/2026-10-07-density-overlap-phase.md), including the explicit source-family and proof-dependency limits.

## Manuscript 001 version 4 scope

[Version 4](preprints/001-strongly-log-concave-brenier/v4/README.txt) is a focused logarithmic-moment continuation using the complete public v3 potential theorem as an explicit proof input. It does not replace v3's broader results or claim to re-prove that input. The [v4 manifest](releases/2026-10-07-v4.json) identifies the changed files.

Its Gaussian logarithmic-target-moment threshold is distinct from 008's source-boundary-vanishing threshold. The former has no additional logarithmic loss at its stated transition; the latter has a necessary logarithmic correction proved by a multiscale construction. The parameters describe different assumptions, so these statements do not conflict and are not counted as duplicate project results.

## Projection geometry version 3

[005 v3](preprints/005-simplex-product-optimum/v3/README.md) extends lower-bound equality from polytopes to all convex bodies, proves qualitative affine stability and a sharp symmetric cone bound, and gives an explicit Cartesian-square spectral amplification theorem. The complete proof and exact replay were disclosed in `43bb307c76ec83d09feb2fe3aa74b2a40e3d2bdc`. The [read-only verification workflow](.github/workflows/projection-rigidity-exact.yml) replays rational checks and byte-identity comparisons; it does not rewrite published files. Historical v1.1 and v2 statements and their scopes are retained.

## Manuscript 001 version 5: source regularity

[Version 5](preprints/001-strongly-log-concave-brenier/v5/README.txt) combines the v4 Gaussian results with an exact minimum-density weight, fixed-source Sobolev little-o refinements, and stronger smooth-source target-tail obstructions. The root-density/Fisher criterion overlaps [008](preprints/008-density-overlap-phase/README.md) and is explicitly cross-credited, not counted twice. Its strict comparison with raw translation ratios and its endpoint qualifications are stated in full. The finite-q and stretched-exponential endpoint lower ratios tend to zero; the assertions are sharp powers, not matching positive endpoint constants or all-small-distance envelopes.

A [six-page supplement](notes/stretched-exponential-sharpness/README.md) proves matching stretched-exponential logarithmic lower bounds for fixed hard-boundary examples. It is a supplement to 001 and 007, not a new numbered paper. The [008 independent audit](reviews/2026-10-07-density-overlap-independent-audit.md) includes expanded exact replays. Historical sources remain unchanged.

See the [source-regularity reconciliation](comparisons/2026-10-07-source-regularity-reconciliation.md) for the overlap among 001 v5, 007 v2 and 008, and the focused earlier boundary-density comparison.

## Critical boundary supplement: slowly varying density factors

The [six-page supplement](notes/critical-boundary-slow-variation/manuscript.pdf), with [complete source](notes/critical-boundary-slow-variation/manuscript.tex) and [scope/build information](notes/critical-boundary-slow-variation/README.txt), extends 008's critical multiscale construction to the specified positive C2 slowly varying factors. It proves a sharp implicit modulus for every sufficiently small target distance and a necessary iterated-logarithm correction at the displayed threshold. Within that exact source family, pure one-third stability is equivalent to the global density-root Sobolev condition; no arbitrary-source necessity claim is made.

The original 008 v1 is unchanged. The supplement explicitly imports its overlap interpolation and global mass-matching mechanism, and the 001 v3 all-P2 potential estimate. It is not a new numbered paper or a priority certification. See the [proof review](reviews/2026-10-07-critical-slow-variation-review.md) and [changed-file manifest](releases/2026-10-07-critical-slow-variation-v1.json).
