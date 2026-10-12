# Pinned distance densities in nested train track models

A complete English manuscript candidate consolidated from four analytically reviewed source notes and their two scoped wording revisions, dated 8 October 2026.

## Files

- `main.pdf`: typeset paper
- `main.tex` and `sections/*.tex`: full editable LaTeX, including all proofs
- `build.sh` and `BUILD.md`: local, non-downloading build instructions
- `SOURCE_MAP.md`: claim, proof, and source coverage
- `sources/`: byte-identical source snapshots, audit, editorial-revision records, and input hash manifest
- `qa/QA_REPORT.md`: compilation and page-by-page visual check
- `SHA256SUMS`: integrity hashes for the prepared manuscript package

## What is proved

The paper studies the original natural distance probabilities of one explicit rational-parameter planar product-digit family. It includes both superlacunary and fixed-ratio stage schedules, Frostman and Hausdorff/packing dimension proofs, two BV/coarea replacement estimates, a fixed positive restriction with bounded jointly continuous densities, and intervals of uniformly positive length in every studied pin's actual distance set. Interval position may vary with the pin.

For the superlacunary schedule and `1 < alpha < 3/2`, the uniform attained exponent is `(2-alpha)/(3-2alpha)`. Failure above that exponent is asserted for pins whose first coordinate is in the horizontal support H, not for the whole pin rectangle. Off H the original density is bounded and locally jointly continuous. At and above `alpha=3/2`, raw densities are bounded and jointly continuous throughout the pin rectangle.

For fixed ratio and `aK>2`, the finite critical endpoint is excluded when `D_K>0`; the raw density is bounded and continuous when `D_K<0`. At `D_K=0`, every finite Lq holds, with only an O(log q) norm upper bound and a double-exponential tail upper bound. No matching lower growth is claimed. There is no continuous-density version for any pin above H. Essential boundedness at these pins remains open. The exact stronger-regularity exceptional sets and their dimensions are stated separately from interval-distance existence.

The paper retains further positive masks, the actual retained-mass normalization, collision and whole-low-pass stability, the nonuniform weighted rectangular-template sufficient condition, and a direct alternative subcritical proof.

## Attribution and status

The near-track/far-track distinction is attributed to Guth, Iosevich, Ou, and Wang. Peres and Schlag are cited as projection-theory background and are not used as a proof input. No historical-priority claim, unrestricted Falconer threshold, professional human peer review, or Lean/formal verification is claimed.

The original four notes received a separate model-based analytic review. Two later clarifications, concerning the nonmembership pin domain and the logarithmic norm upper bound, passed the original reviewer's scoped recheck as reported in the consolidation assignment. The older “not yet audited” lines are retained only inside byte-identical historical snapshots; the new paper gives the updated status. Editorial source-fidelity review of this typeset consolidation is separately recorded in `qa/` and is not a new full mathematical audit.

This is a candidate for the user's review. It has not been submitted or published. No Git operation, attachment delivery, external sharing, new parameter computation, or new mathematical research was performed. Existing TeX resources were reused. Authorship and licensing remain for the user to determine; this packaging step does not assign them.
