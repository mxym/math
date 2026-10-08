# Dimension structure in simplex stability

Read the [complete 32-page paper](source/main.pdf), [editable LaTeX](source/main.tex), [source map](source/SOURCE_MAP.md), and [build instructions](source/README.md).

## Results and limits

For full-dimensional d-polytopes, d >= 3, with **at most d+2 facets**, the paper retains every prescribed maximum-volume inscribed simplex S and its original centroid. The defect exponent is sharp within this class, and the optimal dimensional coefficient divided by d tends to one. It also proves the full single-halfspace-cut maximum classification, actual signed-cofactor defect identities, projection-core bounds, and edge-supported inverse and retention results under their stated conditions.

A comparison core does not replace the prescribed S. Edge support relative to an unrelated simplex does not establish the conditional actual-defect corollary. The general unrestricted O(d) versus O(d²) gap and the exact fixed-d few-facet optimum remain open.

## What this release contains

The [original manuscript ZIP](../../releases/2026-10-08-dimension-structure-manuscript.zip) contains the exact 19 reviewed paper/source files, also preserved unchanged in `source/`. Its SHA-256 is `10dff94652951bc9aa27762e3c3f37c54bb16b33b32c056abe273b55cdca72b6`. The manuscript includes the full written arguments for its new results and the required finite-assignment and actual-facet-enclosure appendices, with its classical standard inputs identified. All TeX inputs lie inside these 19 files.

The separate 55-payload research-source and certificate archive referenced in the frozen source manifest and review records is **not included in this public release**. Its recorded hash identifies the material reviewed at preparation time; it is not a download supplied here. This release is the complete paper and paper source, not a public copy of every underlying research note, exact-checking script or historical evidence record. The separate four certificate suites cannot be rerun from this manuscript-only package.

The paper can be rebuilt from `source/` with the documented configured TeX installation, without that research archive. The retained clean-build evidence for this exact 19-file ZIP records a three-pass build reproducing the supplied PDF byte-for-byte. No compiler or TeX cache is bundled.

## Current review status

The [final-copy report](../../verification/2026-10-08-dimension-structure-simplex-stability/FINAL_COPY_REVIEW.md) and [verification record](../../verification/2026-10-08-dimension-structure-simplex-stability/VERIFICATION.json) report COPY PASS for the exact manuscript. They refer to both this manuscript and the separately held research archive; their research-archive checks do not mean that archive is included here. The copy review adds identified independent focused checks of projection and inverse-minor arguments, without relabelling all prior parent/worker contributions as wholly independent review. Its nine inspected PDF pages are distinct from the preparation record's complete 32-page visual pass.

Preparation-time pending/unpublished labels within the unchanged source snapshot are historical and are superseded by the dated final-copy report. No mathematical source or PDF was edited for publication. These are written proofs and analytic/copy checks; no new result is claimed Lean-formalized, professionally human-peer-reviewed, journal-accepted or priority-certified. Source attributions and existing rights remain; no new license or personal authorship is assigned.

The [publication manifest](../../releases/2026-10-08-dimension-structure-simplex-stability.json) binds the exact files and the limited public release scope.
