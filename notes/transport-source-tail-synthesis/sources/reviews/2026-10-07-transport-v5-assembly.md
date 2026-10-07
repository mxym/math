# Independent mathematical assembly audit: 001 v5

7 October 2026. **Scoped pass:** no mathematical correction to the complete assembled manuscript was required. This is an independent model review, not external human peer review, formal verification, or a new proof of the inherited 001 v3 potential theorem.

## Frozen final identities

- Source SHA-256: `61f7d07e0072e237d9d108fc5a663d6d21d47f1c704958b36c4787cbce533fe4`
- Bibliography SHA-256: `65bc903195ef612a413a0a5f23ecf620ad9d2b954bf2eb1c89e032c90041e7cb`
- PDF SHA-256: `ac39b675676d9fb3ee9ecac34d7082a319b6406d59dda2b7dc82aaa7020fefb6`
- [Final source](../preprints/001-strongly-log-concave-brenier/v5/manuscript.tex), [PDF](../preprints/001-strongly-log-concave-brenier/v5/manuscript.pdf), [artifact record](../preprints/001-strongly-log-concave-brenier/v5/QA.txt).

## Analytic checks

The entire 26-page assembly was checked directly, including every statement and proof, the unlabelled sharpness arguments, constants, zero cases, source-domain conventions and endpoint quantifiers. Earlier independent arguments were comparison material rather than substitutes for this reading.

1. **Minimum-density inequality.** The endpoint minimum controls both translated evaluations. Effective convex domains have null boundaries; no connected density support is assumed. The signed-square substitutions are absolutely integrable, and the potential/error coefficients 12, 6 and 2 are correct. The universal weight mean coefficient seven is attained by an interval indicator.
2. **Sobolev refinements.** The exact first-order weight converges in L1 to `6|∂r|+2(-∂r)_+`. The weak derivative vanishes on the zero set, making the limiting measure absolutely continuous with respect to the source. Boundedness and uniform absolute continuity justify the finite-q and stretched-exponential little-o statements uniformly over the stated target/gradient classes for each fixed density. The finite-q statement excludes q=infinity; the displayed triangular interpolation example verifies that exclusion.
3. **Root-density criterion.** Truncated chain rules retain boundary jumps and justify the global Sobolev condition. The bounded-deficit estimate holds for every signed displacement and yields the stated constant after exact minimization. For density proportional to `exp(-exp(x²))`, all finite score moments are finite while every nonzero inward raw translation ratio has divergent Lp norm. This separates sufficient conditions; no necessity theorem is asserted.
4. **Gaussian and controlled smooth sources.** Polynomial-weight interpolation, dependence-free logarithmic pairing, the rare-halfspace matching, the three-atom one-third obstruction, the second-moment endpoint and dimension-one isometry all have the advertised scope. The best finite-q Gaussian constant has the stated order as q decreases to two. Smooth-source class sharpness is through its Gaussian member, not an assertion of individual sharpness for every source.
5. **Sparse smooth source.** Local finiteness makes the potential smooth; no summability of its huge coefficients is assumed. The doubled-exponential scale gives the necessary stronger relation `P_n=o(log log H_n)`. Global tangent bounds dominate the entire survival integral, including later layers. Mass matching and map/target cost identities are exact. The same fixed source works for all stated moment parameters.
6. **Endpoint distinctions.** Finite-q and stretched-exponential lower ratios tend to zero at their endpoint scales and defeat every stronger power, consistently with the little-o upper estimates. Logarithmic-second-moment lower comparability is only along a sequence. No all-small-distance envelope, reverse-entropy proximity, or optimal numerical constant is claimed. Delaying the first layer yields the stated total-variation and forward-relative-entropy bounds for one fixed source chosen before the target sequence.

## Proof input and attribution corrections

The pinned 001 v3 all-P2 potential theorem was checked for matching hypotheses and constant. This assembly audit does not independently redo its cell-calculus proof. Every transport use supplies that input explicitly; arbitrary BV or Sobolev density regularity is not claimed to imply it.

Two editorial defects were corrected before release. The 007 PDF/main links initially pointed to the extension-only commit; the final bibliography distinguishes the first extension source at `c8d4fa9d7afc28d10123e666af0dfcdfc3f2681d` from the complete assembly at `c450c746ea17a90e4b97ca429193b80692056639`. The shared root-density criterion in already-public 008 is now explicitly cross-credited in the introduction and Fisher section. The final editorial diff preserves all mathematical formulas and theorem/proof environments byte-for-byte. See the [reconciliation](../comparisons/2026-10-07-source-regularity-reconciliation.md).

## Finite checks and rebuilding

Finite sanity checks passed 1,326 signed-square pairs, 3,124 discrete nonnegative-density weight cases, 1,136 root-deficit cases, seven exact rational exponent checks and three limiting-profile checks. All 114 labels resolve. These checks supplement, and do not prove, the analytic assertions.

An independent clean build using only the release inputs produced 26 pages, with no final-log errors, warnings, unresolved references or box warnings. Its layout text is identical to the final PDF. All 26 page renderings were inspected as overview sheets, in addition to the separate full-size page inspection. The source archive and released file hashes were checked independently. Build configuration is recorded in the release files; PDF metadata need not be byte-identical across toolchains.

The HAL full-text comparison remains unfinished and is disclosed as such. This audit does not certify novelty, priority, journal significance, a complete source classification, or absence of every possible error.
