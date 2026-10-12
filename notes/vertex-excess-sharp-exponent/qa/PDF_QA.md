# PDF quality assurance

Final PDF: `vertex_excess_sharp_exponent.pdf`
SHA-256: `1897d4059800e2a7612d65f816c0eb274d844375aebcf1f551144eec56c4fc05`
Pages: 17. Size: 393130 bytes.

## Build and automated checks

- Three-pass pdfLaTeX build completed successfully with TeX Live 2025/dev/Debian.
- Final TeX log has no overfull/underfull boxes, undefined references, or warnings.
- All 74 equation/section/theorem labels resolve; no duplicate labels or unresolved `??` markers in the PDF text.
- Nine packaged input snapshots are byte-identical to their pinned originals.
- The verification script passed 84 exact rational beta-integral cases and 32 core-formula cases with pyramid conversions. These are transcription sanity checks, not proof certification.
- See `verification.json` for the exact result and PDF hash.

## Page-by-page visual inspection

The final PDF was rendered with Poppler at 100 dpi. Every resulting page image was opened and visually inspected after the last TeX change. No clipped text, overlapping equations, missing glyphs, cropped page numbers, or unreadable source paths were found.

- Page 1: PASS. Title, abstract, verification-status boundary and single-page contents.
- Page 2: PASS. Literal invariant, original-centroid excess, theorem constants and sharp limit.
- Page 3: PASS. Literature scope, positive integer cone lemma and mixed-volume display.
- Page 4: PASS. Beta integral, factorial convention, ray collapse and actual-facet corollary.
- Page 5: PASS. Finite assignment statement, determinant witnesses and witness enumeration.
- Page 6: PASS. Weighted anchor selection, clipped estimate and raw facet definitions.
- Page 7: PASS. Pyramid raw identities, normalized original simplex, finite law and moments.
- Page 8: PASS. Actual-defect identity, assignment budget, width, enclosure and facet incidence.
- Page 9: PASS. Multiplicative correction, finite mixed-volume scaling and projection constant.
- Page 10: PASS. Substochastic matching, inverse bootstrap and both all-scale retention statements.
- Page 11: PASS. Unrestricted and bounded retention, determinant block, prescribed nonvertex maxima.
- Page 12: PASS. Endpoint assembly, vertex count parameter and exact truncation core statement.
- Page 13: PASS. Core determinants, m=2 formula and pyramid-invariance statement.
- Page 14: PASS. Pyramid proof, ambient sharp limit and geometric all-direction example.
- Page 15: PASS. Facet vectors, homogeneous brightness ratio and exact source correspondence.
- Page 16: PASS. Retained Lean namespaces and explicit no-new-formalization boundary.
- Page 17: PASS. Complete bibliography and live descriptive DOI/arXiv URLs.

The theorem constants were split into two lines to remove an initial overfull display. The contents was restricted to section entries to keep it together. The bibliography starts on its own page rather than leaving two isolated entries on the last page.

## Scope

This report concerns the prepared PDF, build, and source-fidelity packaging. The supplied original traditional review and the expanded-manuscript source-fidelity receipt are separately labeled under `audit/`. No Lean build, new independent mathematical audit, priority determination, professional peer review, or external publication was performed in this preparation step.
