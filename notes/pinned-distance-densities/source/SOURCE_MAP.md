# Source map and scope preservation

Date: 8 October 2026. The manuscript consolidates the following four revised source snapshots. Each copy under `sources/` is byte-identical to its named input. `sources/source_manifest.json` gives complete original paths, copied paths, and verified hashes.

## Authoritative input identities

- A, positive repair: `aa85b4e46f8752754ce187d8413d200763d87639997f73b0782f874eefb79f81`
- B, phase diagram and intervals, revised: `d6276d83c9d228bf6baabf160a20493440f7e6e3e72f6db9081053bf558fe4b9`
- C, fixed-ratio endpoint switch: `4ab70460deb7c4cce215ab442b2590017001dfbb3ffc4952c5ab81787eef3505`
- D, exact pin strata and boundary, revised: `6aa50a1fea9b49fa1b9e9471f261b1fa996b37c6061e9a2f2bedcc3c097a6f05`

A and C are unchanged from the original reviewed snapshots. B and D contain only the scoped clarifications described below. Historical hashes quoted inside A–D still refer to the frozen historical notes; the current authoritative identities are the hashes above and the input manifest. The copied INDEX is a revised navigation aid, not a separate mathematical input.

The original construction snapshot is supplied for provenance. The new manuscript reproduces the construction and all proof inputs, so it does not depend on following an external relative path into that snapshot. The full analytic report and editorial revision report are copied without alteration. The assignment reported that the original reviewer passed the limited recheck; there is no separate local recheck-receipt file supplied with the inputs.

## Section and proof coverage

### Main file and Section 1

Sources: A §0, B §§1 and 10, C §§1 and 8, D §§1, 4, 7, and 8; complete analytic review §§11–12.

The abstract and three main theorems separate the whole-rectangle uniform upper bounds from nonmembership on `B = H × [0,eta]`. They explicitly state off-H bounded continuity, the attained superlacunary endpoint, the excluded fixed-ratio finite endpoint, and the unresolved boundary L∞ question. The interval theorem uses a uniform length, with pin-dependent interval position. The manuscript is clearly model-specific.

### Section 2, `02_construction.tex`

Sources: A §1, B §§2–3, C §§1–2; original construction for historical continuity.

Includes exact free digit positions, integrality, fixed-prefix conditioning, both realized schedules, vertical separation, all four free-count pieces, Frostman proof, Hausdorff dimension, coordinate singularity and nonatomicity, superlacunary packing dimension, the two fixed-ratio candidate peaks and their difference, exact planar packing dimension, and the actual filled-tail rectangular template. A's fully specified alpha=13/10 realization and its first error exponent are preserved. The obsolete non-L² growth condition is explicitly confined to its historical parameter range.

### Section 3, `03_quadrature.tex`

Sources: A §§2–3, B §§3–4, C §3; full audit §3.

Includes bin-oscillation quadrature, the local output t=r/h, both coarea derivative factors, branch monotonicity, zero-extension variation, both averaging orders, the physical h^-1 conversion, the fixed-band estimate, and the harmonic-bin summation. The pin and positive mask remain identical through each comparison; no cell-count or hidden coordinate-regularity assumption is introduced.

### Section 4, `04_positive_filters.tex`

Sources: A §§4–5, B §§5 and 8, C §4; full audit §§4–5.

Includes summability for both schedules, exact initial and accumulated constants, weighted parent summation, null hard-cut boundaries, weak-limit identification for every pin, polar-coarea continuity of finite stages, promotion from essential supremum to true supremum, raw absolute continuity, weak-L^alpha, and intervals in the actual compact distance image in both directions. The retained mass and interval position caveats are explicit.

### Section 5, `05_superlacunary.tex`

Sources: A §6.2 and lower-bound portion of §6, B §§6–7, D §3; full audit §6.

Preserves the auxiliary band h/A, harmonic outer increment, global aligned-bin masses, exact vertical filled-tail bound, product-law interpolation, endpoint identity c(1-1/q*)=a, inherited 2^-n/2 gain, direct alpha=3/2 L∞ estimate, weak-limit identification, and uniform continuity for the bounded regime. The complete track lower bound works for every p1 in H including coding endpoints, with no vertical pin-Cantor condition. The summary quantifiers follow revised B.

### Section 6, `06_fixed_ratio.tex`

Sources: C §§5–7; full audit §7.

Includes the exact inner exponent D_K-c(K+1)/q, outer growth condition, all three D_K regimes, proof that q_K>1, the localized integral contradiction on |U_j|→0 at q=q_K, the weaker finite-q sufficient condition, both numerical examples already in the sources, and the endpoint-switch explanation. The sufficient K inequalities are not presented as necessary thresholds.

### Section 7, `07_exceptional_pins.tex`

Sources: all of revised D; full audit §§8–9.

Includes the compact off-H gap argument, full exceptional sets Bad_q and Bad_C0 in every regime, exact horizontal and curtain dimensions with direct product/Baire justification, identities linking D_K and s_K, boundary dimension example, minimal-distance localized mass obstruction to continuity, all finite boundary norms, only the O(log q) norm upper bound, double-exponential upper tail, and the finite-interval double-exponential integral. L∞ on the boundary curtain remains open and no matching lower norm growth or tail asymptotic is asserted.

### Section 8, `08_stability.tex`

Sources: A §§7–8, B §9, C §8; full audit §10.

Includes actual positive-measure domination, squared-L² normalization by the true retained mass, inherited decreasing masks and their additional pair-mass budget, the need to check local cell fractions, endpoint and shared-pin perturbations, whole-low-pass control, and the weighted nonuniform replacement criterion with all stated hypotheses. The low-pass comparison is written with the triangular positive-definite kernel explicitly noted as a valid route in the audit; it is an expanded elementary justification of the source's same comparison, not an additional result. The nonuniform criterion does not inherit the exact Lq endpoints merely from summable errors.

### Section 9, `09_scope.tex`

Sources: A §§8–9, B §10, C §8, D §§7–8; full audit §12.

Keeps all important exclusions: irrational parameters without a rounding proof, rotations, exact nonproduct endpoints, arbitrary pre-replacement masks, local mass retention, unrestricted common-pin recursion, arbitrary-mask frequency-shell decay, unknown finite-endpoint Lorentz behavior, unknown boundary L∞, and unproved sharpness of logarithmic norm growth. No-TV restoration is explained through the existing non-L² conclusion and elementary weak L² compactness.

### Appendix A, `appendix_subcritical.tex`

Source: A §6.1.

Preserves the alternative conditional subcritical argument in full: theta, gamma_q, wider auxiliary band, conditional support-length gain, inner mass and coarea bounds, balanced L exponents, parent-mass summation, and superlacunary convergence. This argument is not substituted for the separate endpoint proof.

## Consolidation choices

- Repeated construction and quadrature proofs are stated once and explicitly cross-referenced. No substantive theorem or proof mechanism is replaced by an appeal to a general Falconer theorem.
- Source symbol B for the pin curtain becomes calligraphic B in LaTeX to avoid collision with the vertical sampling integer B. Other parameters retain their source meanings.
- Source prose and ASCII formulas are typeset in normal mathematical notation. Expository theorem numbering is new; this map preserves the source correspondences.
- The reviewed lower-bound pin domain is consistently enlarged from original pins E_- to the full proven set H×[0,eta], exactly as D establishes. It is never enlarged to the entire pin rectangle.
- Boundary terminology consistently says logarithmic norm upper bound. No matching lower rate is inserted.
- Obsolete pre-review status sentences are removed from the consolidated prose and preserved in untouched source copies. The paper describes model-based analytic review without claiming human peer review, formal verification, or historical priority.

## Literature attribution

The primary GIOW source was checked at `https://arxiv.org/html/1808.09346v1`, §1.2 (near-track peaks, distant-track smoothing) and the section listing for §6 (train-track examples). Bibliographic identity was checked at `https://arxiv.org/abs/1808.09346`. The paper's discussion is limited to that attribution and the distinction between GIOW's general construction and this positive band restriction.

The Peres–Schlag reference is `https://doi.org/10.1215/S0012-7094-00-10222-0`, whose canonical title is “Smoothness of projections, Bernoulli convolutions, and the dimension of exceptions.” It is cited only as classical background, never as an imported proof obligation or a novelty claim.

This was editorial verification of supplied background attribution, not a comprehensive literature search or a claim about the currently best general dimension threshold.
