# Source regularity: reconciliation of 001 v5, 007 v2, and 008 v1

Date: 7 October 2026. This note records mathematical scope and overlap, not novelty or priority certification.

## Shared and distinct results

- The BV finite-q and target-tail rates already occur in 001 v3 and 007 v1. Re-deriving them with an explicit bounded weight does not create a second project result.
- The fixed smooth full-support finite-q and q=2 counterexample already occurs in [007 v2](https://github.com/mxym/math/blob/c450c746ea17a90e4b97ca429193b80692056639/preprints/007-tail-brenier-stability/v2/main.tex). Logarithmic-second-moment and Gaussian-proximity conclusions can be obtained by adapting its rare-cell geometry. These are extensions of that construction, not separate discoveries of the basic geometry.
- The minimum-density/root-density sufficient condition in 001 v5 overlaps [008 v1](https://github.com/mxym/math/blob/9af06fa4cadaa80e176ed633a7176ed7f2e813db/preprints/008-density-overlap-phase/v1/main.tex). It is cross-credited and counted once. The fourth-moment Fisher threshold and complete boundary-family classification, including the necessary critical logarithm, are developed in 008.
- Additional 001 v5 statements are the exact bounded-weight mean and first-order limit; fixed-source W1,1 uniform little-o improvements; a strict root-density versus raw-ratio separation; and the stronger smooth-source scale separation needed for stretched-exponential logarithmic-power obstructions. The finite-q and stretched-exponential endpoint ratios tend to zero, so these statements do not assert matching positive endpoint constants.
- The Gaussian logarithmic-second-moment and finite-q constant-order results in v5 were already public in 001 v4. They are retained rather than newly counted.

## A relevant earlier source-boundary result

Letrouit–Mérigot, *Gluing methods for quantitative stability of optimal transport maps*, [version 3, Theorem 1.10](https://arxiv.org/html/2411.04908v3#S1.SS3), treats densities comparable to a power of distance to the boundary on bounded Lipschitz domains, with targets in a fixed compact set. It gives a potential estimate with W1 exponent one half and a source-dependent map exponent below or equal to one sixth. Thus stability for degenerating boundary densities is an existing subject, not new here. Its stated theorem is not the finite-target-moment sharp phase diagram for the particular unbounded product source in 008. This comparison distinguishes the displayed statements only; it does not establish that no equivalent result exists elsewhere.

The HAL item *Sharp stability of Brenier maps via quantitative regularity of potentials* remains a bibliographic reference whose full text has not been retrieved in this review. Its landing page was inaccessible to the available reader on 7 October 2026. No theorem is attributed to it from its title alone.

## Proof dependency

The transport upper bounds in this comparison require the all-P2 centered-potential theorem of 001 v3 or another explicitly proved potential estimate. Arbitrary BV/Sobolev source regularity alone is not asserted to imply that input. Lower constructions and standalone interpolation results have their own stated hypotheses. None of these model audits is external human peer review or proof-assistant verification.
