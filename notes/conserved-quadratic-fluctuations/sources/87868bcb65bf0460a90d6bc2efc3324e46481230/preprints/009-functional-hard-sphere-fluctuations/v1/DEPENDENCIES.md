# Exact mathematical dependency inventory

## Pinned primary source

OpenAI, *Hard-sphere fluctuations on the regular Boltzmann lifespan*, 23 September 2026.
Commit: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build

Every mathematical use of this source refers to that snapshot. Section 2 of the manuscript states the operational imported package and its exact TeX labels. The following inventory distinguishes imported inputs from new proofs; no private note is a theorem input.

## Imported inputs

- **Kinetic assumptions and normalization:** source section 01, `ass:kinetic`, `eq:grand-canonical`, `eq:empirical-fluctuation`; smooth whole-space probability density with spatially summable Gaussian density/gradient norms, classical Boltzmann solution on the prescribed finite interval with the stated Gaussian bound, diameter ε, activity μ = ε⁻², ordinary spherical surface measure.
- **Initial ensemble:** source section 02, `prop:initial`, `eq:initial-factorial-upper`, `eq:initial-N-moments`; actual normalized factorial masses at most one and uniform fixed moments of N/μ. These are unweighted microscopic statements.
- **Pasted flow and analytic envelopes:** source section 03, `def:dhm-history`, `thm:dhm-package`, the cutoffs and positive history estimates; source section 04, `prop:one-root`; source section 06, `eq:sharp-input-bounds`. Γ and L are fixed independently of subsequently chosen moment orders.
- **Actual marked hierarchy:** source section 04, `lem:autonomous-partition`, `lem:one-slab-expansion`, `lem:marked-regrouping`, `lem:diagram-labels`, `lem:stopped-variation`, `thm:marked-expansion`; exact finite retained component expansion, connected factorial-cumulant inversion, unweighted exponentially small total-variation errors, and arbitrary-power high-complexity tails.
- **Chronological and spatial coordinates:** source section 06, `lem:sharp-merger-coordinates`, `eq:sharp-jacobian`, `eq:sharp-activity`, `eq:sharp-scaling`; one independent phase coordinate per global birth line, no new coordinate at an identity continuation, free merger coordinates, determined redundant intersections, zero extension of missing branches, and physical-link gains.
- **Combinatorics and energy:** source section 06, `lem:sharp-factorials`, `eq:sharp-line-count`, `lem:sharp-summability`; original label factorials, bounded-complexity polynomial exceptional counts, common-translation integrated Gaussian envelope, active energy bounded by birth energy, and n − a = q + 1 + p for connected histories.
- **Initial links and tails:** source section 02 initial connected bounds and source section 06, `eq:sharp-initial-link`, `eq:sharp-scaling`, initial-tail deletion, and proof of `thm:sharp-cumulants`; physical links gain εᵖ and nonphysical tails permit an arbitrary chosen power.
- **Unweighted cumulants and Gaussian target:** source section 06, `thm:sharp-cumulants`, `eq:sharp-full-cumulant`; section 07, `prop:cumulant-clt`; section 02, `prop:gaussian-target`, `eq:target-covariance`, `eq:target-field-bound`. The target's C₀→L² bound is used for Schwartz cutoff identification. The finite factorial-to-ordinary identity from section 07 is also reproved in the paper.
- **True-flow discrepancy:** source section 05, `prop:cutoff`; full-time discrepancy probability O(ε^(21/20)) under the common initial-data coupling. The exact-centering argument of section 08, `lem:center-transfer`, is reproduced. This input does not transfer true-flow high moments.
- **Path version and flow regularity:** Deng–Hani–Ma, arXiv:2408.07818v3, Proposition 1.2 and Appendix A, proof of Proposition 4.5, items (1) and (5). These give the almost-everywhere finite-collision flow, deterministic-time collision-null sets, and absolute continuity through the countably branched capped maps. The paper explicitly uses the outgoing right-continuous versions.
- **Nuclear-space path theorem:** Mitoma, Annals of Probability 11 (1983), 989–999; the precise strong-dual generalized-J₁ form is stated in Jakubowski, *On the Skorokhod topology* (1986), §5.II, Theorem 5.5. Jakubowski equation (1.3), Proposition 1.6(i), and Proposition 5.3 give the topology, continuous-path restriction, and Borel/cylindrical equality used in section 8.

## New arguments proved in this paper

1. Repeated-pair erased Gaussian innovation and its quantitative return probability.
2. Forest rank-one transfer, nonneighbor residual-time slope, and truncated logarithmic small-ball integration.
3. Full source-family squared-flux summation preserving both factorials, including all allowed later contacts and interfaces.
4. Uniform tree-window localization and quantitative actual pasted-law increment cumulants after microscopic error inversion.
5. Passive collision-count record extension and calendar-equivariant quotient-coordinate majorant, including lifetime-domain and physical-link handling.
6. Actual incidence cumulants, microscopic modulus, and two-grid finite-family functional convergence.
7. All-Schwartz extension, strong-dual path-law realization and tightness, countable Borel determination and extraction, strong continuity, and full path-law identification for both flows.

## Scope and attribution

The new cyclic rate is √(ε[1 + log(1/ε)]); its repeated-pair sector has rate √ε. These are connected-history bounds used to establish functional convergence. No quantitative rate of convergence of the Gaussian fluctuation law or limiting covariance is proved. The paper retains the source's existing Gaussian test-scale interpretation and does not assert that the collision drift maps Schwartz space to itself. No publication-priority or external-peer-review claim is made.
