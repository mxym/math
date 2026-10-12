# Proof dependencies and exact sources

## New proof chain

- [QUADRATIC_DIMENSION_THEOREM.md](QUADRATIC_DIMENSION_THEOREM.md): theorem, invariant, all-branch assembly, uniform constant, asymptotic order, and scope.
- [INTRINSIC_NORM_CONVERSION.md](INTRINSIC_NORM_CONVERSION.md): maximum-simplex asymmetry, intrinsic dispersion, multiplicative weight correction, Minkowski conversion, and the zero/endpoints.
- [intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md](intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md): exact relative vertex caps, determinant matching, every-maximum bootstrap, global quadratic bridge, and general support-width cap.

## Special imported statements

- [imports/weighted_anchors.md](imports/weighted_anchors.md), Sections 1–5: the complete integrated-assignment theorem in any fixed norm. Here $A$ and $B$ are first absolute determinant moments, $D=B-A$, and $V$ is the unnormalized lifted determinant. The denominator $B$ and the indicator $1_{V>0}$ are retained. Sections 6–8 record geometric consequences and explicitly qualified abstract-law limitations.
- [imports/POLYNOMIAL_REFINEMENT.md](imports/POLYNOMIAL_REFINEMENT.md), Section 1: the same first-moment anchor proof in compact form; Section 3: actual cone-law normalization, dispersion, and $D/B=(d+1)e/[1+(d+1)e]$. Section 2 concerns maximum-simplex normalization; it is not the cone-law section.
- [sources/entry005-v3.md](sources/entry005-v3.md), Section 4, especially Proposition 4.1: the cone-law pushforward of $h_K(u)dS_K(u)/(d|K|)$ under $u\mapsto u/h_K(u)$, its exact probabilistic representation, and applicability to general full-dimensional convex bodies. Sections 2–3 supply the first-moment defect framework. The source's other theorems are historical context rather than new claims of this supplement.
- [sources/sharp-simplex-proof.tex](sources/sharp-simplex-proof.tex) and [sources/truncation-proof.tex](sources/truncation-proof.tex): original sharp-stability and actual truncation proofs; the deficit exponent is not modified.
- [imports/SQUARE_PYRAMID_LOWER_BOUND.md](imports/SQUARE_PYRAMID_LOWER_BOUND.md): the already-audited realized lower bound.

Cauchy's projection formula, surface-area centering and total-mass identities, volume first variation, and Minkowski's first inequality are the classical inputs. Attribution is preserved in the exact source copies and NOTICE.md.

SOURCE_PINS.json binds every public dependency to its current bytes. AUDITED_ORIGINAL_SOURCE_HASHES.json binds the original audit's 11 source records to those public copies without conflating original and derivative hashes. The archived original source-pin manifest is reproduced without change as sources/HISTORICAL_SOURCE_PINS.json; its `sources/` paths are resolved from this release root.

Historical manuscripts are preserved byte-for-byte and may have relative links to their original repository neighbors. Such neighbors are not silently represented as bundled files. Consult the source's exact public commit URL in SOURCE_PINS.json for that original context. No future commit URL is assumed.
