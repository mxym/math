# Source overlap and target tails in quantitative Brenier stability

A research-programme guide to manuscripts [001](../../preprints/001-strongly-log-concave-brenier/README.md), [007](../../preprints/007-tail-brenier-stability/README.md) and [008](../../preprints/008-density-overlap-phase/README.md). The programme organizes their existing proof drafts; it is not a merged paper or an additional theorem. All numbered entries, historical versions, proof sources and disclosure records retain their identity. No novelty, priority, external-peer-review or formal-verification claim is implied.

## Common framework and dependencies

Write `q>2` for the target moment order, `s=q/(q-2)` for the source information order, `b` for boundary vanishing order, and `beta` for the logarithmic target-moment parameter. These parameters describe different conditions.

The common route is: centered-potential stability, convex-gradient interpolation using minimum-density weights or coordinate slices, quantitative source overlap, then a target-tail or target-moment bound. The lower constructions test different parts of this route.

Transport upper bounds need the separate input `(P): ||U_mu-U_nu||L2(rho) <= A_rho W2(mu,nu)` for all finite-second-moment targets. [001 v3, Theorem 1.1](../../preprints/001-strongly-log-concave-brenier/v3/manuscript.tex) proves it for full-dimensional strongly log-concave sources, including extended-valued convex potentials with hard boundaries, with `A_rho=sqrt(2/kappa)`. Theorem 1.4 gives the compact full-dimensional log-concave companion with `A_rho=(1+sqrt(162))R` for support in `B_R`. The proofs and completion are in Sections 2–7 and 13. BV, W1,1 or root-Sobolev regularity alone does not supply (P).

[001 v5, Lemma 3.1](../../preprints/001-strongly-log-concave-brenier/v5/manuscript.tex) supplies the common minimum-density inequality for arbitrary densities and proper convex potentials, under its integrability hypotheses. Its BV consequence has tail coefficient 8. [007 v2, Theorem 1.1](../../preprints/007-tail-brenier-stability/v2/main.tex) retains a separate slice/coarea proof with the sharper actual-tail coefficient 4. The common framework does not replace that stronger estimate.

## Results to count once and results to retain separately

| Result and proof home | Coverage and relationship |
| --- | --- |
| [001 v3](../../preprints/001-strongly-log-concave-brenier/v3/manuscript.tex), Theorems 1.5 and 1.7; [007 v1](../../preprints/007-tail-brenier-stability/v1/main.tex), Theorem 3.1 and Corollary 3.2 | The shared general tail and finite-q transport upper bounds are counted once. The transport exponent is `(q-2)/(3q-2)`. Fixed hard-boundary sharpness is proved in 001 v3, Sections 11–12; it is not a second transport-sharpness result of 007 v1. |
| [007 v2](../../preprints/007-tail-brenier-stability/v2/main.tex), Theorems 1.1 and 2.1 | Independent BV-density interpolation and sharp potential-to-gradient exponent. Its one-dimensional ramp is an interpolation example, not a transport-map obstruction. These results are retained from v1. |
| [001 v3](../../preprints/001-strongly-log-concave-brenier/v3/manuscript.tex), Theorem 1.6 and Corollary 9.2 | One-third stability for the standard Gaussian at each fixed finite q>2 and for the specified controlled full-support sources. Gaussian sharpness does not assert sharpness for every other member of the controlled class. |
| [007 v2](../../preprints/007-tail-brenier-stability/v2/main.tex), Proposition 5.1, Corollaries 5.2–5.3 and Theorem 6.1 | Raw-ratio sufficient condition; superquadratic positive examples; one-third sharpness for each displayed fixed product source; and one fixed smooth full-support strongly log-concave source with all finite-q optimal powers `(q-2)/(3q-2)` and q=2 failure. |
| [001 v4](../../preprints/001-strongly-log-concave-brenier/v4/manuscript.tex), Theorems 1.1–1.3, retained in [v5](../../preprints/001-strongly-log-concave-brenier/v5/manuscript.tex) | Gaussian logarithmic-target-moment exponent `min(1/3,beta/(beta+1))`, loss-free beta=1/2 transition, controlled-source extension, and best homogeneous finite-q constant of order `[q/(q-2)]^(1/6)` in dimension at least two. Count the retained results once. |
| [001 v5](../../preprints/001-strongly-log-concave-brenier/v5/manuscript.tex), Lemma 3.1, Proposition 4.1, Proposition 5.1 and Theorems 5.2–5.3 | Arbitrary-density minimum-weight inequality, sharp mean coefficient seven, W1,1 first-order limit, and fixed-source uniform little-o improvements for finite q and stretched-exponential moments. Little-o need not improve the exponent. |
| [001 v5](../../preprints/001-strongly-log-concave-brenier/v5/manuscript.tex), Theorem 6.1; [008 v1](../../preprints/008-density-overlap-phase/v1/main.tex), Theorem 1.2 and Section 2 | Shared global density-root/generalized-Fisher sufficient criterion, counted once. The root is zero-extended; boundary jumps cannot be ignored. 001 v5, Proposition 6.2 separates this condition from raw-ratio control. |
| [008 v1](../../preprints/008-density-overlap-phase/v1/main.tex), Theorems 1.1–1.2 and Sections 3–7 | Distinct explicit boundary-family phase diagram and sharp universal finite-Fisher target-moment threshold q=4. The latter is a class statement, not a necessary threshold for every individual source. |
| [001 v5](../../preprints/001-strongly-log-concave-brenier/v5/manuscript.tex), Theorem 12.1 | Smooth-source Gaussian proximity and simultaneous tail obstructions. Finite-q and q=2 geometry overlaps 007; logarithmic moments/proximity adapt it, and stronger scale separation supplies the stretched-exponential logarithmic-power obstruction. |
| [Hard-boundary stretched-exponential supplement](../stretched-exponential-sharpness/stretched_exponential_sharpness.tex), Theorem 1 | Existing synthesis of 001 geometry and 007's upper estimate, with positive matching endpoint ratios for fixed uniform-cube and cube-truncated-Gaussian sources. Count once as a supplement. |
| [Critical slowly-varying boundary supplement](../critical-boundary-slow-variation/manuscript.tex), Theorem 1 and following corollaries | Exact implicit inverse modulus and necessary log-log example, for the supplement's specified C2 logarithmic-derivative and strongly-convex-extension hypotheses. Arbitrary slow variation is not the stated source class. |

001 v3 also retains its conditional-cell transport/covariance, normalized-barycenter, finite-cell and Wasserstein-curve-lifting results. A focused map-stability paper would not exhaust that broader record. See the existing [parallel reconciliation](../../comparisons/2026-10-07-modulus-tail-reconciliation.md), [source-regularity reconciliation](../../comparisons/2026-10-07-source-regularity-reconciliation.md) and [density-phase comparison](../../comparisons/2026-10-07-density-overlap-phase.md) for attribution and overlap.

## Endpoint distinctions

For the explicit 008 family with first marginal proportional to `x^b exp(-x²/2)` on x>0 and the stated transverse bumps:

- Below `b=2/(q-2)`, the exact modulus is `w^((b+1)(q-2)/(2q+(b+1)(q-2)))`.
- At equality, it is `w^(1/3)(1+log(1/w))^((q-2)/(3q))`; the critical lower construction uses a growing number of atoms.
- Above equality, it is `w^(1/3)`.

These are two-sided bounds for every sufficiently small distance for that family. They are different from the Gaussian target-logarithmic threshold beta=1/2, where no additional logarithmic loss is required. They are also different from the universal finite-Fisher threshold q=4.

The slowly-varying supplement retains the exact expression `G(F^-1(w))`, with `H(h)=1+integral_h^a L(x) dx/x`, `F(h)=h^(3/2)H(h)^(1/(2s))` and `G(h)=h^(1/2)H(h)^(1/(2s))`. Substituting `h=w^(2/3)` is not valid for all its admissible factors. Its pure-one-third/root-Sobolev equivalence is restricted to that family.

For the smooth steep-layer examples, an optimal finite-q power can coexist with a vanishing endpoint ratio. 001 v5's stretched-exponential result likewise has optimal logarithmic power but a vanishing endpoint ratio; its logarithmic-second-moment result gives a positive lower comparison along a sequence. These claims are weaker than the all-small-distance two-sided boundary moduli. The hard-boundary stretched-exponential supplement instead gives a positive matching endpoint ratio.

All transport lower obstructions just described require dimension at least two. For an atomless one-dimensional source, the common monotone coupling gives map distance equal to W2. The inherited proof dependencies and original attribution remain those of the linked manuscripts; this guide does not certify a new single-paper assembly.
