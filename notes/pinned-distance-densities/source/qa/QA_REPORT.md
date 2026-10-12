# Final manuscript QA

Date: 8 October 2026.

## Outcome

PASS for local compilation, source fidelity, and rendered-page inspection. The final paper is 20 A4 pages. Its separate source-fidelity receipt is `SOURCE_FIDELITY_RECEIPT.md`.

Final PDF SHA-256:

    4b924ef49a1501424468a8db62c61ca8b2751cab6fbe012f92738d7e53148be5

## Compilation

- Existing pdfLaTeX/TeX resources were reused; no packages or software were installed or downloaded.
- Three passes with shell escape disabled, file-line error reporting, and recorder output.
- The final log contains no TeX error, unresolved reference/citation, missing character, or overfull horizontal/vertical box.
- One first-build overfull display in the definitions of Bad_q and Bad_C0 was corrected by putting the definitions on separate aligned lines. This was a layout-only correction.
- The corrected final PDF, not the first build, was rendered and inspected.
- All four authoritative source hashes and every packaged source copy were verified byte-identical. The originals were not edited.
- A second clean-directory build containing only the TeX sources and build script, with the existing cache explicitly selected, completed successfully and reproduced the final PDF byte-for-byte. Its PDF SHA-256 is identical to the value above; the clean compile log is retained as `clean-build.log`.

## Visual method

Poppler rendered the final PDF at 100 dpi to one PNG per page. All 20 individual page images were opened and visually inspected. Text extraction was used only as a supplementary structure check, not as a substitute for inspecting the rendered pages.

Every page was checked for readable mathematical glyphs, complete equations, consistent margins and numbering, accidental clipping, overlap, broken cross-references, and section transitions. The document uses conventional article typography with AMS theorem/proof formatting. The references occupy a short final page intentionally; no content is missing.

## Page-by-page receipt

- Page 1: title, complete abstract, linked contents; clear and unclipped.
- Page 2: notation and first main theorem, beginning of fixed-ratio theorem; equations and theorem continuation clean.
- Page 3: remaining main results, interval quantifiers, attribution/status, beginning of construction; clean.
- Page 4: prefix conditioning, geometry, schedules, free-count cases; all four cases legible.
- Page 5: Frostman and planar dimensions, beginning of filled tails; clean.
- Page 6: exact template and resolution identities, bin quadrature, fixed-band lemma; clean.
- Page 7: two coarea branches, variation estimates, harmonic gain; no clipped equations.
- Page 8: fixed restriction, limit identification, joint continuity formula, weak integrability statement; clean.
- Page 9: raw weak estimate, actual interval proof, start of endpoint increments; clean.
- Page 10: global band mass and vertical density estimates, attained upper endpoint; clean.
- Page 11: all-horizontal-support track lower bound and fixed-ratio setup; clean.
- Page 12: fixed-ratio upper estimates, localized endpoint failure, numerical comparisons; clean.
- Page 13: off-H proposition and exceptional-set dimensions; clean.
- Page 14: dimension identities and complete boundary noncontinuity proof; clean.
- Page 15: separate aligned Bad definitions, all five classifications, boundary upper estimates; clean.
- Page 16: logarithmic-series and tail proof, domination and mass normalization; clean.
- Page 17: inherited masks, collision perturbations, triangular-kernel comparison, nonuniform theorem start; clean.
- Page 18: nonuniform theorem and proof, scope and open questions; clean.
- Page 19: remaining exclusions and full alternative subcritical argument; clean.
- Page 20: two attributed primary references and working citation targets; clean.

## Editorial safeguards

The abstract, main theorems, phase summaries, and exact-set section consistently distinguish the full pin rectangle from H×[0,eta]. Off-H bounded continuity is explicit. The fixed-ratio boundary is consistently an O(log q) norm upper bound without a matching lower bound, with unresolved L∞ on the horizontal-support pin set. Uniform interval length never becomes a claim of one shared interval. No general Falconer threshold, priority claim, formal verification, or human peer-review claim was added.

This QA does not certify novelty or replace professional mathematical peer review. No publication, Git operation, attachment delivery, or expanded research computation was performed.
