# Independent adversarial audit summary

**Date: 7 October 2026. Verdict: PASS for the intended affine-equivalence class.** The parent thread separately reviewed and reimplemented the mixed upper theorem. Its full audit report and independent checker are maintained separately and are not runtime dependencies of this package.

The audit found no substantive mathematical or certificate gap. Its sole publication-facing clarification was that affine images must be images under invertible affine maps on affine hulls. This package makes that restriction explicit in the theorem, README, dependency map, and PDF. Rank-dropping maps are excluded: allowing them would already make every polytope an affine image of a sufficiently large simplex.

The independently audited conclusion is
\[
\log Q\le \frac{49}{1000}D-\frac{87}{2000}\frac{H^2}{D}
-\frac{11}{2000}\frac{H^4}{D^3},\qquad
2.8534<\Gamma_{\mathcal C}\le e^{1049/1000}<2.855.
\]

The audit read the actual public geometric and spectral dependencies at pinned commit `3360e7191cf564a46d09edcbfbd107c9178bd98f`. It checked normalization, cross weights in the product law, join induction, continuous state coverage, the analytic large-factor lemma, the all-dimensional spectral limit, and the strict comparison with the actual public quadratic constant.

A fresh standard-library reimplementation imported none of the submitted checker code. It used a different logarithm enclosure, direct integer factorials, enumeration of all four finite support corners, and an alternative endpoint-gradient quadratic maximization in the tails. It verified all **19,900 finite rectangles** and **15,568 tail intervals**. Its ordinary and optimized Python reports were byte-identical to each other. Their rational interval endpoints can differ from the submitted reports because the logarithm enclosures differ; both certify the stated strict margins.

The largest finite upper bound occurs at dimensions `(5,5)`, approximately `-0.0015635515023644162`, and the largest tail bound occurs in a cell with small dimension `108`, approximately `-4.482151769730934e-8`. These decimals describe the independently certified exact rational bounds; they are not acceptance criteria. All finite bounds are below `-3/2000`, and all tail bounds are below `-1/100000000`.

The supplemental symbolic reimplementation passed **29 checks** in both Python modes, including the general cancellation and nonnegative-square identities. **24 deliberately corrupted-certificate executions** were rejected, spanning twelve mutation classes in both modes. The pinned inherited lower checker also passed fresh ordinary and optimized replay, including its four built-in corruption controls. The original candidate archive's hashes remained unchanged before and after the audit.

This is model-assisted mathematical review and exact arithmetic replay, not external human peer review or proof-assistant formalization. The audit certifies the restricted recursive class and the displayed ceiling. It does not determine the optimum, improve the inherited limiting lower construction, or certify an unrestricted extremal or priority claim. The literature comparison is documented separately in `literature.md`.
